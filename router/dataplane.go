// Copyright 2020 Anapaya Systems
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//   http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// +gobra

// (VerifiedSCION) the following init-postconditions causes severe slowdowns
// @ initEnsures alreadySet                    != nil && alreadySet.ErrorMem()
// @ initEnsures cannotRoute                   != nil && cannotRoute.ErrorMem()
// @ initEnsures emptyValue                    != nil && emptyValue.ErrorMem()
// @ initEnsures malformedPath                 != nil && malformedPath.ErrorMem()
// @ initEnsures modifyExisting                != nil && modifyExisting.ErrorMem()
// @ initEnsures noSVCBackend                  != nil && noSVCBackend.ErrorMem()
// @ initEnsures unsupportedPathType           != nil && unsupportedPathType.ErrorMem()
// @ initEnsures unsupportedPathTypeNextHeader != nil && unsupportedPathTypeNextHeader.ErrorMem()
// @ initEnsures noBFDSessionFound             != nil && noBFDSessionFound.ErrorMem()
// @ initEnsures noBFDSessionConfigured        != nil && noBFDSessionConfigured.ErrorMem()
// @ initEnsures errBFDDisabled                != nil && errBFDDisabled.ErrorMem()
package router

import (
	"bytes"
	"context"
	"crypto/rand"
	"crypto/subtle"
	"errors"
	"fmt"
	"hash"
	"math/big"
	"net"
	"strconv"
	"sync"
	"syscall"
	"time"

	"github.com/google/gopacket"
	"github.com/google/gopacket/layers"
	"github.com/prometheus/client_golang/prometheus"

	"github.com/scionproto/scion/pkg/addr"
	libepic "github.com/scionproto/scion/pkg/experimental/epic"
	"github.com/scionproto/scion/pkg/log"
	"github.com/scionproto/scion/pkg/private/serrors"
	"github.com/scionproto/scion/pkg/private/util"
	"github.com/scionproto/scion/pkg/scrypto"

	"github.com/scionproto/scion/pkg/slayers"
	"github.com/scionproto/scion/pkg/slayers/path"
	"github.com/scionproto/scion/pkg/slayers/path/empty"
	"github.com/scionproto/scion/pkg/slayers/path/epic"
	"github.com/scionproto/scion/pkg/slayers/path/onehop"
	"github.com/scionproto/scion/pkg/slayers/path/scion"
	"github.com/scionproto/scion/private/topology"
	"github.com/scionproto/scion/private/underlay/conn"
	underlayconn "github.com/scionproto/scion/private/underlay/conn"
	"github.com/scionproto/scion/router/bfd"
	"github.com/scionproto/scion/router/control"
	// @ . "github.com/scionproto/scion/verification/utils/definitions"
	// @ fl "github.com/scionproto/scion/verification/utils/floats"
	// @ sl "github.com/scionproto/scion/verification/utils/slices"
	// @ "github.com/scionproto/scion/verification/utils/seqs"
	// @ socketspec "golang.org/x/net/internal/socket/"
	// @ io "verification/io"
)

const (
	// Number of packets to read in a single ReadBatch call.
	inputBatchCnt = 64

	// TODO(karampok). Investigate whether that value should be higher.  In
	// theory, PayloadLen in SCION header is 16 bits long, supporting a maximum
	// payload size of 64KB. At the moment we are limited by Ethernet size
	// usually ~1500B, but 9000B to support jumbo frames.
	bufSize = 9000

	// hopFieldDefaultExpTime is the default validity of the hop field
	// and 63 is equivalent to 6h.
	hopFieldDefaultExpTime = 63
)

// (VerifiedSCION) acc(Mem(), _) is enough to call every method, given that
// the concrete implementations of this type use internal sync mechanisms to
// obtain write access to the underlying data.
type bfdSession interface {
	// @ pred Mem()

	// (VerifiedSCION) a logger is obtained from ctx through the method Value.
	// @ requires acc(ctx.Mem(), _)
	// @ requires acc(Mem(), _)
	// @ ensures  err != nil ==> err.ErrorMem()
	Run(ctx context.Context) (err error)
	// @ requires  acc(Mem(), _)
	// @ requires  msg.Mem(ub)
	// (VerifiedSCION) an implementation must copy the fields it needs from msg
	// @ preserves sl.AbsSlice_Bytes(ub, 0, len(ub))
	// @ ensures   msg.NonInitMem()
	ReceiveMessage(msg *layers.BFD /*@ , ghost ub []byte @*/)
	// @ requires acc(Mem(), _)
	IsUp() bool
}

// BatchConn is a connection that supports batch reads and writes.
// (VerifiedSCION) the spec of this interface matches that of the methods
// with the same name in private/underlay/conn/Conn.
type BatchConn interface {
	// @ pred Mem()

	// @ requires  acc(Mem(), _)
	// @ requires  forall i int :: { &msgs[i] } 0 <= i && i < len(msgs) ==>
	// @ 	msgs[i].Mem()
	// @ ensures   forall i int :: { &msgs[i] } 0 <= i && i < len(msgs) ==>
	// @ 	(msgs[i].Mem() && msgs[i].HasActiveAddr())
	// @ ensures   err == nil ==> 0 <= n && n <= len(msgs)
	// @ ensures   err == nil ==>
	// @ 	forall i int :: { &msgs[i] } 0 <= i && i < n ==> (
	// @ 		typeOf(msgs[i].GetAddr()) == type[*net.UDPAddr] &&
	// @ 		!msgs[i].HasWildcardPermAddr())
	// @ ensures   err == nil ==>
	// @ 	forall i int :: { &msgs[i] } 0 <= i && i < n ==> msgs[i].GetN() <= len(msgs[i].GetFstBuffer())
	// @ ensures   err != nil ==> err.ErrorMem()
	// contracts for IO-spec
	// @ requires Prophecy(prophecyM)
	// @ requires io.token(place) && MultiReadBio(place, prophecyM)
	// @ preserves dp.Valid()
	// @ ensures  err != nil ==> prophecyM == 0
	// @ ensures  err == nil ==> prophecyM == n
	// @ ensures  io.token(old(MultiReadBioNext(place, prophecyM)))
	// @ ensures  old(MultiReadBioCorrectIfs(place, prophecyM, ifsToIO_ifs(ingressID)))
	// @ ensures  err == nil ==>
	// @	forall i int :: { &msgs[i] } 0 <= i && i < n ==>
	// @	unfolding acc(msgs[i].Mem(), _) in absIO_val(dp, msgs[i].Buffers[0], ingressID) ==
	// @    old(MultiReadBioIO_val(place, n)[i])
	// TODO (Markus): uint16 or option[io.IO_ifs] for ingress
	ReadBatch(msgs underlayconn.Messages /*@, ghost ingressID uint16, ghost prophecyM int, ghost place io.Place, ghost dp io.DataPlaneSpec @*/) (n int, err error)
	// @ requires  acc(addr.Mem(), _)
	// @ requires  acc(Mem(), _)
	// @ preserves acc(sl.AbsSlice_Bytes(b, 0, len(b)), R10)
	// @ ensures   err == nil ==> 0 <= n && n <= len(b)
	// @ ensures   err != nil ==> err.ErrorMem()
	WriteTo(b []byte, addr *net.UDPAddr) (n int, err error)
	// @ requires  acc(Mem(), _)
	// (VerifiedSCION) opted for less reusable spec for WriteBatch for
	// performance reasons.
	// @ requires  len(msgs) == 1
	// @ preserves acc(msgs[0].Mem(), R50) && msgs[0].HasActiveAddr()
	// @ ensures   err == nil ==> 0 <= n && n <= len(msgs)
	// @ ensures   err != nil ==> err.ErrorMem()
	WriteBatch(msgs underlayconn.Messages, flags int) (n int, err error)
	// @ requires Mem()
	// @ ensures  err != nil ==> err.ErrorMem()
	// @ decreases
	Close() (err error)
}

// DataPlane contains a SCION Border Router's forwarding logic. It reads packets
// from multiple sockets, performs routing, and sends them to their destinations
// (after updating the path, if that is needed).
//
// XXX(lukedirtwalker): this is still in development and not feature complete.
// Currently, only the following features are supported:
//   - initializing connections; MUST be done prior to calling Run
type DataPlane struct {
	// (VerifiedSCION) this is morally ghost
	// It is stored in the dataplane in order to retain
	// knowledge that macFactory will not fail
	// @ key *[]byte
	external          map[uint16]BatchConn
	linkTypes         map[uint16]topology.LinkType
	neighborIAs       map[uint16]addr.IA
	internal          BatchConn
	internalIP        net.IP
	internalNextHops  map[uint16]*net.UDPAddr
	svc               *services
	macFactory        func() hash.Hash
	bfdSessions       map[uint16]bfdSession
	localIA           addr.IA
	mtx               sync.Mutex
	running           bool
	Metrics           *Metrics
	forwardingMetrics map[uint16]forwardingMetrics
}

var (
	alreadySet                    = serrors.New("already set")
	invalidSrcIA                  = serrors.New("invalid source ISD-AS")
	invalidDstIA                  = serrors.New("invalid destination ISD-AS")
	invalidSrcAddrForTransit      = serrors.New("invalid source address for transit pkt")
	cannotRoute                   = serrors.New("cannot route, dropping pkt")
	emptyValue                    = serrors.New("empty value")
	malformedPath                 = serrors.New("malformed path content")
	modifyExisting                = serrors.New("modifying a running dataplane is not allowed")
	noSVCBackend                  = serrors.New("cannot find internal IP for the SVC")
	unsupportedPathType           = serrors.New("unsupported path type")
	unsupportedPathTypeNextHeader = serrors.New("unsupported combination")
	noBFDSessionFound             = serrors.New("no BFD sessions was found")
	noBFDSessionConfigured        = serrors.New("no BFD sessions have been configured")
	errBFDDisabled                = serrors.New("BFD is disabled")
)

type scmpError struct {
	TypeCode slayers.SCMPTypeCode
	Cause    error
}

// Gobra cannot currently prove termination of this function,
// because it is not specified how the ErrorMem() of the result
// of serrors.New relates to that of e.
// @ trusted
// @ preserves e.ErrorMem()
// @ ensures   e.IsDuplicableMem() == old(e.IsDuplicableMem())
// @ decreases e.ErrorMem()
func (e scmpError) Error() string {
	// @ unfold e.ErrorMem()
	// @ defer fold e.ErrorMem()
	return serrors.New("scmp", "typecode", e.TypeCode, "cause", e.Cause).Error()
}

// SetIA sets the local IA for the dataplane.
// @ requires  acc(d.Mem(), OutMutexPerm)
// @ requires  !d.IsRunning()
// @ requires  d.LocalIA().IsZero()
// @ requires  !ia.IsZero()
// @ preserves d.mtx.LockP()
// @ preserves d.mtx.LockInv() == MutexInvariant!<d!>;
// @ ensures   acc(d.Mem(), OutMutexPerm)
// @ ensures   !d.IsRunning()
// @ ensures   e == nil
func (d *DataPlane) SetIA(ia addr.IA) (e error) {
	d.mtx.Lock()
	defer d.mtx.Unlock()
	// @ unfold MutexInvariant!<d!>()
	// @ assert !d.IsRunning()
	// @ d.isRunningEq()
	// @ unfold d.Mem()
	// @ defer fold MutexInvariant!<d!>()
	// @ defer fold d.Mem()
	if d.running {
		// @ Unreachable()
		return modifyExisting
	}
	if ia.IsZero() {
		// @ Unreachable()
		return emptyValue
	}
	if !d.localIA.IsZero() {
		// @ Unreachable()
		return alreadySet
	}
	d.localIA = ia
	return nil
}

// SetKey sets the key used for MAC verification. The key provided here should
// already be derived as in scrypto.HFMacFactory.
// @ requires  acc(d.Mem(), OutMutexPerm)
// @ requires  !d.IsRunning()
// @ requires  !d.KeyIsSet()
// @ requires  len(key) > 0
// @ requires  sl.AbsSlice_Bytes(key, 0, len(key))
// @ preserves d.mtx.LockP()
// @ preserves d.mtx.LockInv() == MutexInvariant!<d!>;
// @ ensures   acc(d.Mem(), OutMutexPerm)
// @ ensures   !d.IsRunning()
// @ ensures   res == nil ==> d.KeyIsSet()
func (d *DataPlane) SetKey(key []byte) (res error) {
	// @ share key
	d.mtx.Lock()
	defer d.mtx.Unlock()
	// @ unfold MutexInvariant!<d!>()
	// @ assert !d.IsRunning()
	// @ d.isRunningEq()
	// @ unfold acc(d.Mem(), 1/2)
	// @ d.keyIsSetEq()
	// @ unfold acc(d.Mem(), 1/2)
	// @ defer fold MutexInvariant!<d!>()
	// @ defer fold d.Mem()
	if d.running {
		// @ Unreachable()
		return modifyExisting
	}
	if len(key) == 0 {
		// @ Unreachable()
		return emptyValue
	}
	if d.macFactory != nil {
		// @ Unreachable()
		return alreadySet
	}
	// First check for MAC creation errors.
	if _, err := scrypto.InitMac(key); err != nil {
		return err
	}
	// @ d.key = &key
	verScionTemp :=
		// @ requires acc(&key, _) && acc(sl.AbsSlice_Bytes(key, 0, len(key)), _)
		// @ requires scrypto.ValidKeyForHash(key)
		// @ ensures  acc(&key, _) && acc(sl.AbsSlice_Bytes(key, 0, len(key)), _)
		// @ ensures  h != nil && h.Mem()
		// @ decreases
		func /*@ f @*/ () (h hash.Hash) {
			mac, _ := scrypto.InitMac(key)
			return mac
		}
	// (VerifiedSCION) Gobra cannot currently prove the following assertion, even though it must
	// follow from the structure of the declaration of `verScionTemp` (https://github.com/viperproject/gobra/issues/713).
	// @ assume verScionTemp != nil
	// @ proof verScionTemp implements MacFactorySpec{d.key} {
	// @   return verScionTemp() as f
	// @ }
	d.macFactory = verScionTemp
	return nil
}

// AddInternalInterface sets the interface the data-plane will use to
// send/receive traffic in the local AS. This can only be called once; future
// calls will return an error. This can only be called on a not yet running
// dataplane.
// @ requires  acc(d.Mem(), OutMutexPerm)
// @ requires  !d.IsRunning()
// @ requires  !d.InternalConnIsSet()
// @ requires  conn != nil && conn.Mem()
// @ requires  ip.Mem()
// @ preserves d.mtx.LockP()
// @ preserves d.mtx.LockInv() == MutexInvariant!<d!>;
// @ ensures   acc(d.Mem(), OutMutexPerm)
// @ ensures   !d.IsRunning()
func (d *DataPlane) AddInternalInterface(conn BatchConn, ip net.IP) error {
	d.mtx.Lock()
	defer d.mtx.Unlock()
	// @ unfold MutexInvariant!<d!>()
	// @ assert !d.IsRunning()
	// @ d.isRunningEq()
	// @ unfold acc(d.Mem(), 1/2)
	// @ d.internalIsSetEq()
	// @ unfold acc(d.Mem(), 1/2)
	if d.running {
		// @ Unreachable()
		return modifyExisting
	}
	if conn == nil {
		// @ Unreachable()
		return emptyValue
	}
	if d.internal != nil {
		// @ Unreachable()
		return alreadySet
	}
	d.internal = conn
	d.internalIP = ip
	// @ fold d.Mem()
	// @ fold MutexInvariant!<d!>()
	return nil
}

// AddExternalInterface adds the inter AS connection for the given interface ID.
// If a connection for the given ID is already set this method will return an
// error. This can only be called on a not yet running dataplane.
// @ requires  conn != nil && conn.Mem()
// @ preserves acc(d.Mem(), OutMutexPerm)
// @ preserves !d.IsRunning()
// @ preserves d.mtx.LockP()
// @ preserves d.mtx.LockInv() == MutexInvariant!<d!>;
func (d *DataPlane) AddExternalInterface(ifID uint16, conn BatchConn) error {
	d.mtx.Lock()
	defer d.mtx.Unlock()
	// @ unfold MutexInvariant!<d!>()
	// @ assert !d.IsRunning()
	// @ d.isRunningEq()
	// @ unfold d.Mem()
	if d.running {
		// @ Unreachable()
		return modifyExisting
	}
	if conn == nil {
		// @ Unreachable()
		return emptyValue
	}
	// @ ghost if d.external != nil { unfold acc(accBatchConn(d.external), 1/2) }
	if _, existsB := d.external[ifID]; existsB {
		// @ establishAlreadySet()
		// @ ghost if d.external != nil { fold acc(accBatchConn(d.external), 1/2) }
		// @ fold d.Mem()
		// @ fold MutexInvariant!<d!>()
		return serrors.WithCtx(alreadySet, "ifID", ifID)
	}
	// @ ghost if d.external != nil { fold acc(accBatchConn(d.external), 1/2) }
	if d.external == nil {
		d.external = make(map[uint16]BatchConn)
		// @ fold accBatchConn(d.external)
	}
	// @ unfold accBatchConn(d.external)
	d.external[ifID] = conn
	// @ fold accBatchConn(d.external)
	// @ fold d.Mem()
	// @ fold MutexInvariant!<d!>()
	return nil
}

// AddNeighborIA adds the neighboring IA for a given interface ID. If an IA for
// the given ID is already set, this method will return an error. This can only
// be called on a yet running dataplane.
// @ requires  !remote.IsZero()
// @ preserves acc(d.Mem(), OutMutexPerm)
// @ preserves !d.IsRunning()
// @ preserves d.mtx.LockP()
// @ preserves d.mtx.LockInv() == MutexInvariant!<d!>;
func (d *DataPlane) AddNeighborIA(ifID uint16, remote addr.IA) error {
	d.mtx.Lock()
	defer d.mtx.Unlock()
	// @ unfold MutexInvariant!<d!>()
	// @ d.isRunningEq()
	// @ unfold d.Mem()
	if d.running {
		// @ Unreachable()
		return modifyExisting
	}
	if remote.IsZero() {
		// @ Unreachable()
		return emptyValue
	}
	if _, existsB := d.neighborIAs[ifID]; existsB {
		// @ establishAlreadySet()
		// @ fold d.Mem()
		// @ fold MutexInvariant!<d!>()
		return serrors.WithCtx(alreadySet, "ifID", ifID)
	}
	if d.neighborIAs == nil {
		d.neighborIAs = make(map[uint16]addr.IA)
	}
	d.neighborIAs[ifID] = remote
	// @ fold d.Mem()
	// @ fold MutexInvariant!<d!>()
	return nil
}

// AddLinkType adds the link type for a given interface ID. If a link type for
// the given ID is already set, this method will return an error. This can only
// be called on a not yet running dataplane.
// @ preserves acc(d.Mem(), OutMutexPerm)
// @ preserves !d.IsRunning()
// (VerifiedSCION) unlike all other setter methods, this does not lock d.mtx.
// This was reported in https://github.com/scionproto/scion/issues/4282.
// @ preserves MutexInvariant!<d!>()
func (d *DataPlane) AddLinkType(ifID uint16, linkTo topology.LinkType) error {
	// @ unfold acc(d.Mem(), OutMutexPerm)
	if _, existsB := d.linkTypes[ifID]; existsB {
		// @ establishAlreadySet()
		// @ fold acc(d.Mem(), OutMutexPerm)
		return serrors.WithCtx(alreadySet, "ifID", ifID)
	}
	// @ fold acc(d.Mem(), OutMutexPerm)
	// @ unfold MutexInvariant!<d!>()
	// @ d.isRunningEq()
	// @ unfold d.Mem()
	// @ defer fold MutexInvariant!<d!>()
	// @ defer fold d.Mem()
	if d.linkTypes == nil {
		d.linkTypes = make(map[uint16]topology.LinkType)
	}
	d.linkTypes[ifID] = linkTo
	return nil
}

// AddExternalInterfaceBFD adds the inter AS connection BFD session.
// @ trusted
// @ requires false
func (d *DataPlane) AddExternalInterfaceBFD(ifID uint16, conn BatchConn,
	src, dst control.LinkEnd, cfg control.BFD) error {

	d.mtx.Lock()
	defer d.mtx.Unlock()
	if d.running {
		return modifyExisting
	}
	if conn == nil {
		return emptyValue
	}
	var m bfd.Metrics
	if d.Metrics != nil {
		labels := prometheus.Labels{
			"interface":       fmt.Sprint(ifID),
			"isd_as":          d.localIA.String(),
			"neighbor_isd_as": dst.IA.String(),
		}
		m = bfd.Metrics{
			Up:              d.Metrics.InterfaceUp.With(labels),
			StateChanges:    d.Metrics.BFDInterfaceStateChanges.With(labels),
			PacketsSent:     d.Metrics.BFDPacketsSent.With(labels),
			PacketsReceived: d.Metrics.BFDPacketsReceived.With(labels),
		}
	}
	s := newBFDSend(conn, src.IA, dst.IA, src.Addr, dst.Addr, ifID, d.macFactory())
	return d.addBFDController(ifID, s, cfg, m)
}

// getInterfaceState checks if there is a bfd session for the input interfaceID and
// returns InterfaceUp if the relevant bfdsession state is up, or if there is no BFD
// session. Otherwise, it returns InterfaceDown.
// @ preserves acc(d.Mem(), R5)
func (d *DataPlane) getInterfaceState(interfaceID uint16) control.InterfaceState {
	// @ unfold acc(d.Mem(), R5)
	// @ defer fold acc(d.Mem(), R5)
	bfdSessions := d.bfdSessions
	// @ ghost if bfdSessions != nil {
	// @		unfold acc(accBfdSession(d.bfdSessions), R20)
	// @		defer fold acc(accBfdSession(d.bfdSessions), R20)
	// @ }
	// (VerifiedSCION) had to rewrite this, as Gobra does not correctly
	// implement short-circuiting.
	if bfdSession, ok := bfdSessions[interfaceID]; ok {
		// @ assert interfaceID in domain(d.bfdSessions)
		// @ assert bfdSession in range(d.bfdSessions)
		// @ assert bfdSession != nil
		if !bfdSession.IsUp() {
			return control.InterfaceDown
		}
	}
	return control.InterfaceUp
}

// (VerifiedSCION) marked as trusted because we currently do not support bfd.Session
// @ trusted
// @ requires  false
func (d *DataPlane) addBFDController(ifID uint16, s *bfdSend, cfg control.BFD,
	metrics bfd.Metrics) error {

	if cfg.Disable {
		return errBFDDisabled
	}
	if d.bfdSessions == nil {
		d.bfdSessions = make(map[uint16]bfdSession)
	}

	// Generate random discriminator. It can't be zero.
	discInt, err := rand.Int(rand.Reader, big.NewInt(0xfffffffe))
	if err != nil {
		return err
	}
	disc := layers.BFDDiscriminator(uint32(discInt.Uint64()) + 1)
	d.bfdSessions[ifID] = &bfd.Session{
		Sender:                s,
		DetectMult:            layers.BFDDetectMultiplier(cfg.DetectMult),
		DesiredMinTxInterval:  cfg.DesiredMinTxInterval,
		RequiredMinRxInterval: cfg.RequiredMinRxInterval,
		LocalDiscriminator:    disc,
		ReceiveQueueSize:      10,
		Metrics:               metrics,
	}
	return nil
}

// AddSvc adds the address for the given service. This can be called multiple
// times for the same service, with the address added to the list of addresses
// that provide the service.
// @ requires  a != nil && acc(a.Mem(), R10)
// @ preserves acc(d.Mem(), OutMutexPerm)
// @ preserves !d.IsRunning()
// @ preserves d.mtx.LockP()
// @ preserves d.mtx.LockInv() == MutexInvariant!<d!>;
func (d *DataPlane) AddSvc(svc addr.HostSVC, a *net.UDPAddr) error {
	d.mtx.Lock()
	// @ unfold MutexInvariant!<d!>()
	// @ d.isRunningEq()
	defer d.mtx.Unlock()
	if a == nil {
		return emptyValue
	}
	// @ preserves d.Mem()
	// @ ensures   unfolding d.Mem() in d.svc != nil
	// @ decreases
	// @ outline(
	// @ unfold d.Mem()
	if d.svc == nil {
		d.svc = newServices()
	}
	// @ fold d.Mem()
	// @ )
	// @ unfold acc(d.Mem(), R15)
	// @ assert acc(d.svc.Mem(), _)
	d.svc.AddSvc(svc, a)
	if d.Metrics != nil {
		labels := serviceMetricLabels(d.localIA, svc)
		// @ requires acc(&d.Metrics, R20)
		// @ requires acc(d.Metrics.Mem(), _)
		// @ requires acc(labels, _)
		// @ ensures  acc(&d.Metrics, R20)
		// @ decreases
		// @ outline (
		// @ unfold acc(d.Metrics.Mem(), _)
		// @ fl.ZeroLessOne64()
		// @ assert d.Metrics.ServiceInstanceChanges != nil
		// @ assert d.Metrics.ServiceInstanceCount   != nil
		d.Metrics.ServiceInstanceChanges.With(labels).Add(float64(1))
		d.Metrics.ServiceInstanceCount.With(labels).Add(float64(1))
		// @ )
	}
	// @ fold acc(d.Mem(), R15)
	// @ fold MutexInvariant!<d!>()
	return nil
}

// DelSvc deletes the address for the given service.
// (VerifiedSCION) the spec here is definitely weird. Even though
// the lock is acquired here, there is no check that the router is
// not yet running, thus acquiring the lock is not enough to guarantee
// absence of race conditions. To specify that the router is not running,
// we need to pass perms to d.Mem(), but if we do this, then we don't need
// the lock invariant to perform the operations in this function.
// @ requires  a != nil && acc(a.Mem(), R10)
// @ preserves acc(d.Mem(), OutMutexPerm/2)
// @ preserves d.mtx.LockP()
func (d *DataPlane) DelSvc(svc addr.HostSVC, a *net.UDPAddr) error {
	d.mtx.Lock()
	defer d.mtx.Unlock()
	if a == nil {
		return emptyValue
	}
	// @ unfold acc(d.Mem(), R40)
	// @ ghost defer fold acc(d.Mem(), R40)
	if d.svc == nil {
		return nil
	}
	d.svc.DelSvc(svc, a)
	if d.Metrics != nil {
		labels := serviceMetricLabels(d.localIA, svc)
		// @ unfold acc(d.Metrics.Mem(), _)
		// @ fl.ZeroLessOne64()
		d.Metrics.ServiceInstanceChanges.With(labels).Add(float64(1))
		d.Metrics.ServiceInstanceCount.With(labels).Add(float64(-1))
	}
	return nil
}

// AddNextHop sets the next hop address for the given interface ID. If the
// interface ID already has an address associated this operation fails. This can
// only be called on a not yet running dataplane.
// @ requires  a != nil && a.Mem()
// @ preserves acc(d.Mem(), OutMutexPerm)
// @ preserves !d.IsRunning()
// @ preserves d.mtx.LockP()
// @ preserves d.mtx.LockInv() == MutexInvariant!<d!>;
func (d *DataPlane) AddNextHop(ifID uint16, a *net.UDPAddr) error {
	d.mtx.Lock()
	defer d.mtx.Unlock()
	// @ unfold MutexInvariant!<d!>()
	// @ d.isRunningEq()
	// @ unfold d.Mem()
	// @ defer fold MutexInvariant!<d!>()
	// @ defer fold d.Mem()
	if d.running {
		return modifyExisting
	}
	if a == nil {
		return emptyValue
	}
	// @ ghost if d.internalNextHops != nil { unfold accAddr(d.internalNextHops) }
	if _, existsB := d.internalNextHops[ifID]; existsB {
		// @ fold accAddr(d.internalNextHops)
		// @ establishAlreadySet()
		return serrors.WithCtx(alreadySet, "ifID", ifID)
	}
	if d.internalNextHops == nil {
		d.internalNextHops = make(map[uint16]*net.UDPAddr)
	}
	// @ defer fold accAddr(d.internalNextHops)
	d.internalNextHops[ifID] = a
	return nil
}

// AddNextHopBFD adds the BFD session for the next hop address.
// If the remote ifID belongs to an existing address, the existing
// BFD session will be re-used.
// @ trusted
// @ requires false
func (d *DataPlane) AddNextHopBFD(ifID uint16, src, dst *net.UDPAddr, cfg control.BFD,
	sibling string) error {

	d.mtx.Lock()
	defer d.mtx.Unlock()
	if d.running {
		return modifyExisting
	}

	if dst == nil {
		return emptyValue
	}

	for k, v := range d.internalNextHops {
		if v.String() == dst.String() {
			if c, ok := d.bfdSessions[k]; ok {
				d.bfdSessions[ifID] = c
				return nil
			}
		}
	}
	var m bfd.Metrics
	if d.Metrics != nil {
		labels := prometheus.Labels{"isd_as": d.localIA.String(), "sibling": sibling}
		m = bfd.Metrics{
			Up:              d.Metrics.SiblingReachable.With(labels),
			StateChanges:    d.Metrics.SiblingBFDStateChanges.With(labels),
			PacketsSent:     d.Metrics.SiblingBFDPacketsSent.With(labels),
			PacketsReceived: d.Metrics.SiblingBFDPacketsReceived.With(labels),
		}
	}

	s := newBFDSend(d.internal, d.localIA, d.localIA, src, dst, 0, d.macFactory())
	return d.addBFDController(ifID, s, cfg, m)
}

// Run starts running the dataplane. Note that configuration is not possible
// after calling this method.
// @ requires  acc(d.Mem(), OutMutexPerm)
// @ requires  !d.IsRunning()
// @ requires  d.InternalConnIsSet()
// @ requires  d.KeyIsSet()
// @ requires  d.SvcsAreSet()
// @ requires  d.MetricsAreSet()
// @ requires  d.PreWellConfigured()
// (VerifiedSCION) here, the spec still uses a private field.
// @ requires  d.mtx.LockP()
// @ requires  d.mtx.LockInv() == MutexInvariant!<d!>;
// @ requires  ctx != nil && ctx.Mem()
// contracts for IO-spec
// @ requires dp.Valid()
// @ requires d.DpAgreesWithSpec(dp)
// @ requires io.token(place) && dp.dp3s_iospec_ordered(state, place)
func (d *DataPlane) Run(ctx context.Context /*@, ghost place io.Place, ghost state io.IO_dp3s_state_local, ghost dp io.DataPlaneSpec @*/) error {
	// @ share d, ctx
	d.mtx.Lock()
	// @ unfold MutexInvariant!<d!>()
	// @ assert !d.IsRunning()
	// @ d.isRunningEq()

	// @ requires  acc(&d, R50)
	// @ requires  acc(&d.running, runningPerm)
	// @ requires  d.Mem() && !d.IsRunning()
	// @ requires  d.InternalConnIsSet()
	// @ requires  d.KeyIsSet()
	// @ requires  d.SvcsAreSet()
	// @ requires  d.MetricsAreSet()
	// @ requires  d.PreWellConfigured()
	// @ requires  d.DpAgreesWithSpec(dp)
	// @ ensures   acc(&d, R50)
	// @ ensures   MutexInvariant!<d!>()
	// @ ensures   d.Mem() && d.IsRunning()
	// @ ensures   d.InternalConnIsSet()
	// @ ensures   d.KeyIsSet()
	// @ ensures   d.SvcsAreSet()
	// @ ensures   d.MetricsAreSet()
	// @ ensures   d.PreWellConfigured()
	// @ ensures   d.DpAgreesWithSpec(dp)
	// @ decreases
	// @ outline (
	// @ reveal d.PreWellConfigured()
	// @ reveal d.DpAgreesWithSpec(dp)
	// @ unfold d.Mem()
	d.running = true
	// @ fold MutexInvariant!<d!>()
	// @ fold d.Mem()
	// @ reveal d.PreWellConfigured()
	// @ reveal d.DpAgreesWithSpec(dp)
	// @ )
	// @ ghost ioLockRun, ioSharedArgRun := InitSharedInv(dp, place, state)
	d.initMetrics( /*@ dp @*/ )

	read /*@@@*/ :=
		// (VerifiedSCION) Due to issue https://github.com/viperproject/gobra/issues/723,
		// there is currently an incompletness when calling closures that capture variables
		// from (Viper) methods where they were not allocated. To address that, we introduce
		// dPtr as an helper parameter. It always receives the value &d.
		// @ requires acc(dPtr, _)
		// @ requires let d := *dPtr in
		// @ 	acc(&d.external, _) && acc(&d.linkTypes, _)                       &&
		// @ 	acc(&d.neighborIAs, _) && acc(&d.internal, _)                     &&
		// @ 	acc(&d.internalIP, _) && acc(&d.internalNextHops, _)              &&
		// @ 	acc(&d.svc, _) && acc(&d.macFactory, _) && acc(&d.bfdSessions, _) &&
		// @ 	acc(&d.localIA, _) && acc(&d.running, _) && acc(&d.Metrics, _)    &&
		// @ 	acc(&d.forwardingMetrics, _) && acc(&d.key, _)
		// @ requires let d := *dPtr in
		// @ 	acc(d.Mem(), _) && d.WellConfigured()
		// @ requires let d := *dPtr in d.getValSvc() != nil
		// @ requires let d := *dPtr in d.getValForwardingMetrics() != nil
		// @ requires let d := *dPtr in (0 in d.getDomForwardingMetrics())
		// @ requires let d := *dPtr in (ingressID in d.getDomForwardingMetrics())
		// @ requires let d := *dPtr in d.macFactory != nil
		// @ requires rd != nil && acc(rd.Mem(), _)
		// contracts for IO-spec
		// @ requires dp.Valid()
		// @ requires let d := *dPtr in
		// @ 	acc(d.Mem(), _) && d.DpAgreesWithSpec(dp)
		// @ requires acc(ioLock.LockP(), _) && ioLock.LockInv() == SharedInv!< dp, ioSharedArg !>;
		func /*@ rc @*/ (ingressID uint16, rd BatchConn, dPtr **DataPlane /*@, ghost ioLock *sync.Mutex, ghost ioSharedArg SharedArg, ghost dp io.DataPlaneSpec @*/) {
			// @ ghost ioIngressID := ifsToIO_ifs(ingressID)
			d := *dPtr
			msgs := conn.NewReadMessages(inputBatchCnt)
			// @ requires forall i int :: { &msgs[i] } 0 <= i && i < len(msgs) ==>
			// @ 	msgs[i].Mem() && msgs[i].GetAddr() == nil
			// @ ensures  forall i int :: { &msgs[i] } 0 <= i && i < len(msgs) ==>
			// @ 	msgs[i].Mem() &&
			// @ 	msgs[i].HasActiveAddr() &&
			// @ 	msgs[i].GetAddr() == nil
			// @ decreases
			// @ outline(
			// @ invariant 0 <= i0 && i0 <= len(msgs)
			// @ invariant forall i int :: { &msgs[i] } i0 <= i && i < len(msgs) ==>
			// @ 	msgs[i].Mem() && msgs[i].GetAddr() == nil
			// @ invariant forall i int :: { &msgs[i] } 0 <= i && i < i0 ==>
			// @ 	msgs[i].Mem() && msgs[i].GetAddr() == nil && msgs[i].HasActiveAddr()
			// @ decreases len(msgs) - i0
			for i0 := 0; i0 < len(msgs); i0 += 1 {
				// (VerifiedSCION) changed a range loop in favor of a normal loop
				// to be able to perform this unfold.
				// @ unfold msgs[i0].Mem()
				msg := msgs[i0]
				// @ ensures sl.AbsSlice_Bytes(tmp, 0, len(tmp))
				// @ decreases
				// @ outline(
				tmp := make([]byte, bufSize)
				// @ assert forall i int :: { &tmp[i] } 0 <= i && i < len(tmp) ==> acc(&tmp[i])
				// @ fold sl.AbsSlice_Bytes(tmp, 0, len(tmp))
				// @ )
				// @ assert msgs[i0] === msg
				msg.Buffers[0] = tmp
				// @ msgs[i0].IsActive = true
				// @ fold msgs[i0].Mem()
			}
			// @ )
			// @ ensures writeMsgInv(writeMsgs)
			// @ decreases
			// @ outline (
			writeMsgs := make(underlayconn.Messages, 1)
			writeMsgs[0].Buffers = make([][]byte, 1)
			// @ fold sl.AbsSlice_Bytes(writeMsgs[0].OOB, 0, len(writeMsgs[0].OOB))
			// @ sl.NilAcc_Bytes()
			// @ fold writeMsgInv(writeMsgs)
			// @ )

			processor := newPacketProcessor(d, ingressID)
			var scmpErr /*@@@*/ scmpError

			// @ invariant acc(&scmpErr)
			// @ invariant forall i int :: { &msgs[i] } 0 <= i && i < len(msgs) ==>
			// @ 	msgs[i].Mem()
			// @ invariant writeMsgInv(writeMsgs)
			// @ invariant acc(dPtr, _) && *dPtr === d
			// @ invariant acc(&d.external, _) && acc(&d.linkTypes, _)                &&
			// @ 	acc(&d.neighborIAs, _) && acc(&d.internal, _)                     &&
			// @ 	acc(&d.internalIP, _) && acc(&d.internalNextHops, _)              &&
			// @ 	acc(&d.svc, _) && acc(&d.macFactory, _) && acc(&d.bfdSessions, _) &&
			// @ 	acc(&d.localIA, _) && acc(&d.running, _) && acc(&d.Metrics, _)    &&
			// @ 	acc(&d.forwardingMetrics, _) && acc(&d.key, _)
			// @ invariant acc(d.Mem(), _) && d.WellConfigured()
			// @ invariant d.getValSvc() != nil
			// @ invariant d.getValForwardingMetrics() != nil
			// @ invariant 0 in d.getDomForwardingMetrics()
			// @ invariant ingressID in d.getDomForwardingMetrics()
			// @ invariant acc(rd.Mem(), _)
			// @ invariant processor.sInit() && processor.sInitD() === d
			// @ invariant acc(ioLock.LockP(), _) && ioLock.LockInv() == SharedInv!< dp, ioSharedArg !>
			for d.running {
				// Multi recv event
				// @ ghost ioLock.Lock()
				// @ unfold SharedInv!< dp, ioSharedArg !>()
				// @ ghost t, s := *ioSharedArg.Place, *ioSharedArg.State
				// @ ghost numberOfReceivedPacketsProphecy := AllocProphecy()
				// @ ExtractMultiReadBio(dp, t, numberOfReceivedPacketsProphecy, s)
				// @ MultiUpdateElemWitness(t, numberOfReceivedPacketsProphecy, ioIngressID, s, ioSharedArg)
				// @ ghost ioValSeq := MultiReadBioIO_val(t,numberOfReceivedPacketsProphecy)

				// @ ghost sN := MultiReadBioUpd(t, numberOfReceivedPacketsProphecy, s)
				// @ ghost tN := MultiReadBioNext(t, numberOfReceivedPacketsProphecy)
				// @ assert dp.dp3s_iospec_ordered(sN, tN)
				pkts, err := rd.ReadBatch(msgs /*@, ingressID, numberOfReceivedPacketsProphecy, t , dp @*/)
				// @ ghost *ioSharedArg.State = sN
				// @ ghost *ioSharedArg.Place = tN
				// @ MultiElemWitnessConv(ioSharedArg.IBufY, ioIngressID, ioValSeq)
				// @ fold SharedInv!< dp, ioSharedArg !>()
				// @ ioLock.Unlock()
				// End of multi recv event

				// @ assert forall i int :: { &msgs[i] } 0 <= i && i < len(msgs) ==> msgs[i].Mem()
				// @ assert err == nil ==>
				// @ 	forall i int :: { &msgs[i] } 0 <= i && i < pkts ==> msgs[i].GetN() <= len(msgs[i].GetFstBuffer())
				if err != nil {
					log.Debug("Failed to read batch", "err", err)
					// error metric
					continue
				}
				if pkts == 0 {
					continue
				}
				// @ assert pkts <= len(msgs)
				// @ assert forall i int :: { &msgs[i] } 0 <= i && i < pkts ==>
				// @ 	!msgs[i].HasWildcardPermAddr()
				// @ assert forall i int :: { &msgs[i] } 0 <= i && i < pkts ==>
				// @ 	msgs[i].GetN() <= len(msgs[i].GetFstBuffer())

				// (VerifiedSCION) using regular for loop instead of range loop to avoid unnecessary
				// complications with permissions
				// @ invariant acc(&scmpErr)
				// @ invariant forall i int :: { &msgs[i] } 0 <= i && i < len(msgs) ==> msgs[i].Mem()
				// @ invariant writeMsgInv(writeMsgs)
				// @ invariant acc(dPtr, _) && *dPtr === d
				// @ invariant acc(&d.external, _) && acc(&d.linkTypes, _)                &&
				// @ 	acc(&d.neighborIAs, _) && acc(&d.internal, _)                     &&
				// @ 	acc(&d.internalIP, _) && acc(&d.internalNextHops, _)              &&
				// @ 	acc(&d.svc, _) && acc(&d.macFactory, _) && acc(&d.bfdSessions, _) &&
				// @ 	acc(&d.localIA, _) && acc(&d.running, _) && acc(&d.Metrics, _)    &&
				// @ 	acc(&d.forwardingMetrics, _) && acc(&d.key, _)
				// @ invariant acc(d.Mem(), _) && d.WellConfigured()
				// @ invariant d.getValSvc() != nil
				// @ invariant d.getValForwardingMetrics() != nil
				// @ invariant 0 in d.getDomForwardingMetrics()
				// @ invariant ingressID in d.getDomForwardingMetrics()
				// @ invariant acc(rd.Mem(), _)
				// @ invariant pkts <= len(msgs)
				// @ invariant 0 <= i0 && i0 <= pkts
				// @ invariant forall i int :: { &msgs[i] } i0 <= i && i < len(msgs) ==>
				// @ 	msgs[i].HasActiveAddr()
				// @ invariant forall i int :: { &msgs[i] } i0 <= i && i < pkts ==>
				// @ 	typeOf(msgs[i].GetAddr()) == type[*net.UDPAddr]
				// @ invariant forall i int :: { &msgs[i] } 0 <= i && i < pkts ==>
				// @ 	msgs[i].GetN() <= len(msgs[i].GetFstBuffer())
				// @ invariant processor.sInit() && processor.sInitD() === d
				for i0 := 0; i0 < pkts; i0++ {
					// @ assert &msgs[:pkts][i0] == &msgs[i0]
					// @ preserves 0 <= i0 && i0 < pkts && pkts <= len(msgs)
					// @ preserves acc(msgs[i0].Mem(), R1)
					// @ ensures   p === msgs[:pkts][i0].GetMessage()
					// @ outline(
					// @ unfold acc(msgs[i0].Mem(), R1)
					p := msgs[:pkts][i0]
					// @ fold acc(msgs[i0].Mem(), R1)
					// @ )
					// @ assert msgs[i0].GetN() <= len(msgs[i0].GetFstBuffer())
					// @ d.getForwardingMetricsMem(ingressID)
					// @ unfold acc(forwardingMetricsMem(d.forwardingMetrics[ingressID], ingressID), _)
					// input metric
					inputCounters := d.forwardingMetrics[ingressID]
					// @ assert acc(inputCounters.InputPacketsTotal.Mem(), _)
					// @ assert acc(inputCounters.InputBytesTotal.Mem(), _)
					// @ prometheus.CounterMemImpliesNonNil(inputCounters.InputPacketsTotal)
					// @ prometheus.CounterMemImpliesNonNil(inputCounters.InputBytesTotal)
					inputCounters.InputPacketsTotal.Inc()
					// @ assert msgs[i0].GetN() == p.N
					// (VerifiedSCION) Gobra still does not fully support floats
					// @ fl.CastPreservesOrder64(0, p.N)
					inputCounters.InputBytesTotal.Add(float64(p.N))

					srcAddr := p.Addr.(*net.UDPAddr)
					// @ ghost m := &msgs[:pkts][i0]
					// @ unfold m.Mem()
					// @ assert p.Buffers === m.Buffers
					// @ assert acc(&p.Buffers[0])
					// @ assert p.N <= len(p.Buffers[0])
					// @ sl.SplitRange_Bytes(p.Buffers[0], 0, p.N, writePerm)
					tmpBuf := p.Buffers[0][:p.N]
					// @ assert sl.AbsSlice_Bytes(tmpBuf, 0, p.N)
					// @ assert sl.AbsSlice_Bytes(tmpBuf, 0, len(tmpBuf))
					result, err /*@ , addrAliasesPkt @*/ := processor.processPkt(tmpBuf, srcAddr)
					// @ fold scmpErr.Mem()
					switch {
					case err == nil:
						// @ unfold scmpErr.Mem()
					case errors.As(err, &scmpErr):
						// @ unfold d.validResult(result, addrAliasesPkt)
						// @ ghost if addrAliasesPkt  && result.OutAddr != nil {
						// @ 	apply acc(result.OutAddr.Mem(), R15) --* acc(sl.AbsSlice_Bytes(tmpBuf, 0, len(tmpBuf)), R15)
						// @ }
						// @ unfold scmpErr.Mem()
						if !scmpErr.TypeCode.InfoMsg() {
							log.Debug("SCMP", "err", scmpErr, "dst_addr", p.Addr)
						}
						// SCMP go back the way they came.
						result.OutAddr = srcAddr
						result.OutConn = rd
						// @ addrAliasesPkt = false
						// @ fold d.validResult(result, addrAliasesPkt)
					default:
						// @ unfold d.validResult(result, addrAliasesPkt)
						// @ ghost if addrAliasesPkt {
						// @ 	apply acc(result.OutAddr.Mem(), R15) --* acc(sl.AbsSlice_Bytes(tmpBuf, 0, len(tmpBuf)), R15)
						// @ }
						// @ sl.CombineRange_Bytes(p.Buffers[0], 0, p.N, writePerm)
						// @ assert acc(m)
						// @ assert sl.AbsSlice_Bytes(m.OOB, 0, len(m.OOB))
						// @ assert (m.Addr != nil ==> acc(m.Addr.Mem(), _))
						// @ assert 0 <= m.N
						// @ msgs[:pkts][i0].IsActive = false
						// @ fold msgs[:pkts][i0].Mem()
						log.Debug("Error processing packet", "err", err)
						// @ assert acc(inputCounters.DroppedPacketsTotal.Mem(), _)
						// @ prometheus.CounterMemImpliesNonNil(inputCounters.DroppedPacketsTotal)
						inputCounters.DroppedPacketsTotal.Inc()
						// @ unfold scmpErr.Mem()
						continue
					}
					if result.OutConn == nil { // e.g. BFD case no message is forwarded
						// @ unfold d.validResult(result, addrAliasesPkt)
						// @ ghost if addrAliasesPkt {
						// @ 	apply acc(result.OutAddr.Mem(), R15) --* acc(sl.AbsSlice_Bytes(tmpBuf, 0, len(tmpBuf)), R15)
						// @ }
						// @ sl.CombineRange_Bytes(p.Buffers[0], 0, p.N, writePerm)
						// @ msgs[:pkts][i0].IsActive = false
						// @ fold msgs[:pkts][i0].Mem()
						continue
					}

					// Write to OutConn; drop the packet if this would block.
					// Use WriteBatch because it's the only available function that
					// supports MSG_DONTWAIT.
					// @ unfold d.validResult(result, addrAliasesPkt)
					// @ unfold writeMsgInv(writeMsgs)
					writeMsgs[0].Buffers[0] = result.OutPkt
					// @ writeMsgs[0].WildcardPerm = !addrAliasesPkt
					// @ writeMsgs[0].IsActive = true
					writeMsgs[0].Addr = nil
					if result.OutAddr != nil { // don't assign directly to net.Addr, typed nil!
						writeMsgs[0].Addr = result.OutAddr
					}
					// @ sl.NilAcc_Bytes()
					// @ fold acc(writeMsgs[0].Mem(), R50)
					_, err = result.OutConn.WriteBatch(writeMsgs, syscall.MSG_DONTWAIT)
					// @ unfold acc(writeMsgs[0].Mem(), R50)
					// @ ghost if addrAliasesPkt && result.OutAddr != nil {
					// @	apply acc(result.OutAddr.Mem(), R15) --* acc(sl.AbsSlice_Bytes(tmpBuf, 0, len(tmpBuf)), R15)
					// @ }
					// @ sl.CombineRange_Bytes(p.Buffers[0], 0, p.N, writePerm)
					// @ msgs[:pkts][i0].IsActive = false
					// @ fold msgs[:pkts][i0].Mem()
					// @ fold writeMsgInv(writeMsgs)
					if err != nil {
						// @ requires err != nil && err.ErrorMem()
						// @ decreases
						// @ outline (
						var errno /*@@@*/ syscall.Errno
						// @ assert acc(&errno)
						// @ fold errno.Mem()
						errorsAs := errors.As(err, &errno)
						// @ unfold errno.Mem()
						if !errorsAs ||
							!(errno == syscall.EAGAIN || errno == syscall.EWOULDBLOCK) {
							log.Debug("Error writing packet", "err", err)
							// error metric
						}
						// @ )
						// @ assert acc(inputCounters.DroppedPacketsTotal.Mem(), _)
						// @ prometheus.CounterMemImpliesNonNil(inputCounters.DroppedPacketsTotal)
						inputCounters.DroppedPacketsTotal.Inc()
						continue
					}
					// @ requires acc(dPtr, _) && *dPtr === d
					// @ requires acc(d.Mem(), _)
					// @ requires result.EgressID in d.getDomForwardingMetrics()
					// @ decreases
					// @ outline(
					// ok metric
					// @ d.getForwardingMetricsMem(result.EgressID)
					// @ unfold acc(forwardingMetricsMem(d.forwardingMetrics[result.EgressID], result.EgressID), _)
					outputCounters := d.forwardingMetrics[result.EgressID]
					// @ assert acc(outputCounters.OutputPacketsTotal.Mem(), _)
					// @ prometheus.CounterMemImpliesNonNil(outputCounters.OutputPacketsTotal)
					outputCounters.OutputPacketsTotal.Inc()
					// @ assert acc(outputCounters.OutputBytesTotal.Mem(), _)
					// @ prometheus.CounterMemImpliesNonNil(outputCounters.OutputBytesTotal)
					// @ fl.CastPreservesOrder64(0, len(result.OutPkt))
					outputCounters.OutputBytesTotal.Add(float64(len(result.OutPkt)))
					// @ )
				}
			}
		}
	// @ unfold acc(d.Mem(), R1)
	// @ assert d.WellConfigured()
	// @ assert 0 in d.getDomForwardingMetrics()
	// @ ghost if d.bfdSessions != nil { unfold acc(accBfdSession(d.bfdSessions), R2) }

	// (VerifiedSCION) we introduce this to avoid problems with the invariants that
	// are generated by Gobra. In particular, the iterator bounds need access to
	// d.bfdSessions, but because it is shared, we need to pass permission to it
	// in the invariant. Unfortunately, the invariants that are passed by the user are
	// put after those that are generated. Introducing this auxioliary variable sidesteps
	// the issue with the encoding.
	bfds := d.bfdSessions

	// @ invariant bfds != nil ==> acc(bfds, R4)
	// @ invariant bfds != nil ==> acc(accBfdSession(bfds), R4)
	// @ invariant acc(&ctx, _) && acc(ctx.Mem(), _)
	// @ decreases len(bfds) - len(visited)
	for k, v := range bfds /*@ with visited @*/ {
		cl :=
			// @ requires c != nil && acc(c.Mem(), _)
			// @ requires acc(&ctx, _) && acc(ctx.Mem(), _)
			func /*@ closure1 @*/ (ifID uint16, c bfdSession) {
				defer log.HandlePanic()
				// @ bfd.EstablishAlreadyRunning()
				if err := c.Run(ctx); err != nil && err != bfd.AlreadyRunning {
					log.Error("BFD session failed to start", "ifID", ifID, "err", err)
				}
			}
		// @ getBfdSessionMem(v, bfds)
		go cl(k, v) // @ as closure1
	}

	// @ ghost if d.external != nil { unfold acc(accBatchConn(d.external), R2) }

	// (VerifiedSCION) we introduce this to avoid problems with the invariants that
	// are generated by Gobra. In particular, the iterator bounds need access to
	// d.bfdSessions, but because it is shared, we need to pass permission to it
	// in the invariant. Unfortunately, the invariants that are passed by the user are
	// put after those that are generated. Introducing this auxioliary variable sidesteps
	// the issue with the encoding.
	externals := d.external

	// @ invariant acc(&read, _) && read implements rc
	// @ invariant acc(&d, _)
	// @ invariant acc(&d.external, _) && d.external === externals
	// @ invariant acc(d.Mem(), _) && d.WellConfigured()
	// @ invariant externals != nil ==> acc(externals, R4)
	// @ invariant externals != nil ==> acc(accBatchConn(externals), R4)
	// (VerifiedSCION) can we drop a few of these perms?
	// @ invariant acc(&d.external, _) && acc(&d.linkTypes, _)                &&
	// @ 	acc(&d.neighborIAs, _) && acc(&d.internal, _)                     &&
	// @ 	acc(&d.internalIP, _) && acc(&d.internalNextHops, _)              &&
	// @ 	acc(&d.svc, _) && acc(&d.macFactory, _) && acc(&d.bfdSessions, _) &&
	// @ 	acc(&d.localIA, _) && acc(&d.running, _) && acc(&d.Metrics, _)    &&
	// @ 	acc(&d.forwardingMetrics, _) && acc(&d.key, _)
	// @ invariant acc(d.Mem(), _) && d.WellConfigured()
	// @ invariant d.getValSvc() != nil
	// @ invariant d.getValForwardingMetrics() != nil
	// @ invariant 0 in d.getDomForwardingMetrics()
	// @ invariant d.macFactory != nil
	// @ invariant dp.Valid()
	// @ invariant d.DpAgreesWithSpec(dp)
	// @ invariant acc(ioLockRun.LockP(), _) && ioLockRun.LockInv() == SharedInv!< dp, ioSharedArgRun !>;
	// @ decreases len(externals) - len(visited)
	for ifID, v := range externals /*@ with visited @*/ {
		cl :=
			// @ requires acc(&read, _) && read implements rc
			// @ requires acc(&d, _)
			// @ requires acc(&d.external, _) && acc(&d.linkTypes, _)                 &&
			// @ 	acc(&d.neighborIAs, _) && acc(&d.internal, _)                     &&
			// @ 	acc(&d.internalIP, _) && acc(&d.internalNextHops, _)              &&
			// @ 	acc(&d.svc, _) && acc(&d.macFactory, _) && acc(&d.bfdSessions, _) &&
			// @ 	acc(&d.localIA, _) && acc(&d.running, _) && acc(&d.Metrics, _)    &&
			// @ 	acc(&d.forwardingMetrics, _) && acc(&d.key, _)
			// @ requires acc(d.Mem(), _) && d.WellConfigured()
			// @ requires d.getValSvc() != nil
			// @ requires d.getValForwardingMetrics() != nil
			// @ requires 0 in d.getDomForwardingMetrics()
			// @ requires i in d.getDomForwardingMetrics()
			// @ requires d.macFactory != nil
			// @ requires c != nil && acc(c.Mem(), _)
			// contracts for IO-spec
			// @ requires dp.Valid()
			// @ requires d.DpAgreesWithSpec(dp)
			// @ requires acc(ioLock.LockP(), _) && ioLock.LockInv() == SharedInv!< dp, ioSharedArg !>;
			func /*@ closure2 @*/ (i uint16, c BatchConn /*@, ghost ioLock *sync.Mutex, ghost ioSharedArg SharedArg, ghost dp io.DataPlaneSpec @*/) {
				defer log.HandlePanic()
				read(i, c, &d /*@, ioLock, ioSharedArg, dp @*/) //@ as rc
			}
		// @ ghost if d.external != nil { unfold acc(accBatchConn(d.external), R50) }
		// @ assert v in range(d.external)
		// @ assert acc(v.Mem(), _)
		// @ d.InDomainExternalInForwardingMetrics3(ifID)
		// @ ghost if d.external != nil { fold acc(accBatchConn(d.external), R50) }
		go cl(ifID, v /*@, ioLockRun, ioSharedArgRun, dp @*/) //@ as closure2
	}
	cl :=
		// @ requires acc(&read, _) && read implements rc
		// @ requires acc(&d, _)
		// @ requires acc(&d.external, _) && acc(&d.linkTypes, _)                 &&
		// @ 	acc(&d.neighborIAs, _) && acc(&d.internal, _)                     &&
		// @ 	acc(&d.internalIP, _) && acc(&d.internalNextHops, _)              &&
		// @ 	acc(&d.svc, _) && acc(&d.macFactory, _) && acc(&d.bfdSessions, _) &&
		// @ 	acc(&d.localIA, _) && acc(&d.running, _) && acc(&d.Metrics, _)    &&
		// @ 	acc(&d.forwardingMetrics, _) && acc(&d.key, _)
		// @ requires acc(d.Mem(), _) && d.WellConfigured()
		// @ requires d.getValSvc() != nil
		// @ requires d.getValForwardingMetrics() != nil
		// @ requires 0 in d.getDomForwardingMetrics()
		// @ requires d.macFactory != nil
		// @ requires c != nil && acc(c.Mem(), _)
		// contracts for IO-spec
		// @ requires dp.Valid()
		// @ requires d.DpAgreesWithSpec(dp)
		// @ requires acc(ioLock.LockP(), _) && ioLock.LockInv() == SharedInv!< dp, ioSharedArg !>;
		func /*@ closure3 @*/ (c BatchConn /*@, ghost ioLock *sync.Mutex, ghost ioSharedArg SharedArg, ghost dp io.DataPlaneSpec @*/) {
			defer log.HandlePanic()
			read(0, c, &d /*@, ioLock, ioSharedArg, dp @*/) //@ as rc
		}
	go cl(d.internal /*@, ioLockRun, ioSharedArgRun, dp @*/) //@ as closure3

	d.mtx.Unlock()
	// @ assert acc(ctx.Mem(), _)
	c := ctx.Done()
	// @ fold PredTrue!<!>()
	// @ assert c.RecvGivenPerm() == PredTrue!<!>
	<-c
	return nil
}

// initMetrics initializes the metrics related to packet forwarding. The
// counters are already instantiated for all the relevant interfaces so this
// will not have to be repeated during packet forwarding.
// @ requires  d.Mem()
// @ requires  d.MetricsAreSet()
// @ requires  d.KeyIsSet()
// @ requires  d.InternalConnIsSet()
// @ requires  d.SvcsAreSet()
// @ requires  d.PreWellConfigured()
// @ requires  d.DpAgreesWithSpec(dp)
// @ ensures   d.Mem()
// @ ensures   d.MetricsAreSet()
// @ ensures   d.WellConfigured()
// @ ensures   0 in d.DomainForwardingMetrics()
// @ ensures   d.InternalConnIsSet()
// @ ensures   d.KeyIsSet()
// @ ensures   d.SvcsAreSet()
// @ ensures   d.DpAgreesWithSpec(dp)
// @ ensures   d.getValForwardingMetrics() != nil
// @ decreases
func (d *DataPlane) initMetrics( /*@ ghost dp io.DataPlaneSpec @*/ ) {
	// @ assert reveal d.PreWellConfigured()
	// @ assert reveal d.DpAgreesWithSpec(dp)
	// @ assert unfolding acc(d.Mem(), _) in
	// @ 	d.dpSpecWellConfiguredLocalIA(dp)     &&
	// @ 	d.dpSpecWellConfiguredNeighborIAs(dp) &&
	// @ 	d.dpSpecWellConfiguredLinkTypes(dp)
	// @ unfold d.Mem()
	// @ assert d.dpSpecWellConfiguredLocalIA(dp)
	// @ assert d.dpSpecWellConfiguredNeighborIAs(dp)
	// @ assert d.dpSpecWellConfiguredLinkTypes(dp)

	// @ preserves acc(&d.forwardingMetrics)
	// @ preserves acc(&d.localIA, R20)
	// @ preserves acc(&d.neighborIAs, R20)
	// @ preserves d.neighborIAs != nil ==> acc(d.neighborIAs, R20)
	// @ preserves acc(&d.Metrics, R20)
	// @ preserves acc(d.Metrics.Mem(), _)
	// @ ensures   acc(d.forwardingMetrics)
	// @ ensures   domain(d.forwardingMetrics) == set[uint16]{0}
	// @ ensures   acc(forwardingMetricsMem(d.forwardingMetrics[0], 0), _)
	// @ decreases
	// @ outline (
	d.forwardingMetrics = make(map[uint16]forwardingMetrics)
	labels := interfaceToMetricLabels(0, d.localIA, d.neighborIAs)
	d.forwardingMetrics[0] = initForwardingMetrics(d.Metrics, labels)
	// @ liftForwardingMetricsNonInjectiveMem(d.forwardingMetrics[0], 0)
	// @ )
	// @ ghost if d.external != nil { unfold acc(accBatchConn(d.external), R15) }
	// @ ghost if d.internalNextHops != nil { unfold acc(accAddr(d.internalNextHops), R15) }

	// (VerifiedSCION) avoids incompletnes
	// when folding acc(forwardingMetricsMem(d.forwardingMetrics[id], id), _)
	// @ fold acc(hideLocalIA(&d.localIA), R15)

	// @ ghost dExternal := d.external
	// @ ghost dInternalNextHops := d.internalNextHops

	// @ invariant acc(hideLocalIA(&d.localIA), R15)
	// @ invariant acc(&d.external, R15)
	// @ invariant d.external != nil ==> acc(d.external, R20)
	// @ invariant d.external === dExternal
	// @ invariant acc(&d.forwardingMetrics) && acc(d.forwardingMetrics)
	// @ invariant domain(d.forwardingMetrics) == set[uint16]{0} union visitedSet
	// @ invariant 0 in domain(d.forwardingMetrics)
	// @ invariant acc(&d.internalNextHops, R15)
	// @ invariant d.internalNextHops === dInternalNextHops
	// @ invariant d.internalNextHops != nil ==> acc(d.internalNextHops, R20)
	// @ invariant domain(d.internalNextHops) intersection domain(d.external) == set[uint16]{}
	// @ invariant acc(&d.neighborIAs, R15)
	// @ invariant d.neighborIAs != nil ==> acc(d.neighborIAs, R15)
	// @ invariant forall i uint16 :: { d.forwardingMetrics[i] } i in domain(d.forwardingMetrics) ==>
	// @ 	acc(forwardingMetricsMem(d.forwardingMetrics[i], i), _)
	// @ invariant acc(&d.Metrics, R15)
	// @ invariant acc(d.Metrics.Mem(), _)
	// @ decreases len(d.external) - len(visitedSet)
	for id := range d.external /*@ with visitedSet @*/ {
		if _, notOwned := d.internalNextHops[id]; notOwned {
			// @ Unreachable()
			continue
		}
		labels = interfaceToMetricLabels(id, ( /*@ unfolding acc(hideLocalIA(&d.localIA), R20) in @*/ d.localIA), d.neighborIAs)
		d.forwardingMetrics[id] = initForwardingMetrics(d.Metrics, labels)
		// @ liftForwardingMetricsNonInjectiveMem(d.forwardingMetrics[id], id)
		// @ assert acc(forwardingMetricsMem(d.forwardingMetrics[id], id), _)
	}
	// @ ghost if d.external != nil { fold acc(accBatchConn(d.external), R15) }
	// @ ghost if d.internalNextHops != nil { fold acc(accAddr(d.internalNextHops), R15) }
	// @ fold accForwardingMetrics(d.forwardingMetrics)
	// @ unfold acc(hideLocalIA(&d.localIA), R15)
	// @ assert d.dpSpecWellConfiguredLocalIA(dp)
	// @ assert d.dpSpecWellConfiguredNeighborIAs(dp)
	// @ assert d.dpSpecWellConfiguredLinkTypes(dp)
	// @ fold d.Mem()
	// @ reveal d.WellConfigured()
	// @ assert reveal d.DpAgreesWithSpec(dp)
}

type processResult struct {
	EgressID uint16
	OutConn  BatchConn
	OutAddr  *net.UDPAddr
	OutPkt   []byte
}

// @ requires acc(&d.macFactory, _) && d.macFactory != nil
// @ requires acc(d.Mem(), _)
// @ ensures  res.sInit() && res.sInitD() == d
// @ decreases
func newPacketProcessor(d *DataPlane, ingressID uint16) (res *scionPacketProcessor) {
	var verScionTmp gopacket.SerializeBuffer
	// @ d.getNewPacketProcessorFootprint()
	verScionTmp = gopacket.NewSerializeBuffer()
	p := &scionPacketProcessor{
		d:         d,
		ingressID: ingressID,
		buffer:    verScionTmp,
		mac:       (d.macFactory() /*@ as MacFactorySpec{d.key} @ */),
		macBuffers: macBuffersT{
			scionInput: make([]byte, path.MACBufferSize),
			epicInput:  make([]byte, libepic.MACBufferSize),
		},
	}
	// @ fold sl.AbsSlice_Bytes(p.macBuffers.scionInput, 0, len(p.macBuffers.scionInput))
	// @ fold slayers.PathPoolMem(p.scionLayer.pathPool, p.scionLayer.pathPoolRaw)
	p.scionLayer.RecyclePaths()
	// @ fold p.scionLayer.NonInitMem()
	// @ fold p.hbhLayer.NonInitMem()
	// @ fold p.e2eLayer.NonInitMem()
	// @ fold p.bfdLayer.NonInitMem()
	// @ fold p.sInit()
	return p
}

// @ preserves p.sInit()
// @ ensures   p.sInitD()         == old(p.sInitD())
// @ ensures   p.sInitRawPkt()    == nil
// @ ensures   p.sInitPath()      == nil
// @ ensures   p.sInitHopField()  == path.HopField{}
// @ ensures   p.sInitInfoField() == path.InfoField{}
// @ ensures   !p.sInitSegmentChange()
// @ ensures   err != nil ==> err.ErrorMem()
// @ decreases
func (p *scionPacketProcessor) reset() (err error) {
	// @ unfold p.sInit()
	// @ defer fold p.sInit()
	p.rawPkt = nil
	//p.scionLayer // cannot easily be reset
	p.path = nil
	p.hopField = path.HopField{}
	p.infoField = path.InfoField{}
	p.segmentChange = false
	if err := p.buffer.Clear(); err != nil {
		return serrors.WrapStr("Failed to clear buffer", err)
	}
	p.mac.Reset()
	p.cachedMac = nil
	return nil
}

// @ requires p.sInit()
// @ requires sl.AbsSlice_Bytes(rawPkt, 0, len(rawPkt))
// @ requires acc(srcAddr.Mem(), _)
// @ requires let d := p.sInitD() in
// @ 	acc(d.Mem(), _) &&
// @ 	d.WellConfigured()        &&
// @ 	d.getValSvc() != nil      &&
// @ 	d.getValForwardingMetrics() != nil
// @ ensures  p.sInit()
// @ ensures  acc(p.sInitD().Mem(), _)
// @ ensures  p.sInitD() == old(p.sInitD())
// @ ensures  p.sInitD().validResult(respr, addrAliasesPkt)
// @ ensures  acc(sl.AbsSlice_Bytes(rawPkt, 0, len(rawPkt)), 1 - R15)
// @ ensures  addrAliasesPkt ==> (
// @ 	respr.OutAddr != nil &&
// @ 	(acc(respr.OutAddr.Mem(), R15) --* acc(sl.AbsSlice_Bytes(rawPkt, 0, len(rawPkt)), R15)))
// @ ensures  !addrAliasesPkt ==> acc(sl.AbsSlice_Bytes(rawPkt, 0, len(rawPkt)), R15)
// @ ensures  respr.OutPkt !== rawPkt && respr.OutPkt != nil ==>
// @ 	sl.AbsSlice_Bytes(respr.OutPkt, 0, len(respr.OutPkt))
// @ ensures  reserr != nil ==> reserr.ErrorMem()
func (p *scionPacketProcessor) processPkt(rawPkt []byte,
	srcAddr *net.UDPAddr) (respr processResult, reserr error /*@ , addrAliasesPkt bool @*/) {

	if err := p.reset(); err != nil {
		// @ fold p.sInitD().validResult(processResult{}, false)
		return processResult{}, err /*@, false @*/
	}
	// @ assert p.sInitD().getValForwardingMetrics() != nil
	// @ unfold p.sInit()
	// @ ghost d := p.d
	p.rawPkt = rawPkt
	p.srcAddr = srcAddr

	// parse SCION header and skip extensions;
	var err error
	// @ ghost var processed seq[bool]
	// @ ghost var offsets   seq[offsetPair]
	// @ ghost var lastLayerIdx int
	p.lastLayer, err /*@ , processed, offsets, lastLayerIdx @*/ = decodeLayers(p.rawPkt, &p.scionLayer, &p.hbhLayer, &p.e2eLayer)
	if err != nil {
		// @ fold p.sInit()
		// @ fold p.sInitD().validResult(processResult{}, false)
		return processResult{}, err /*@, false @*/
	}
	/*@
	ghost var ub []byte
	ghost var ubScionLayer []byte = p.rawPkt
	ghost var ubHbhLayer []byte
	ghost var ubE2eLayer []byte

	ghost llStart := 0
	ghost llEnd := 0
	ghost mustCombineRanges := lastLayerIdx != -1 && !offsets[lastLayerIdx].isNil
	ghost var o offsetPair
	ghost if lastLayerIdx == -1 {
		ub = p.rawPkt
	} else {
		if offsets[lastLayerIdx].isNil {
			ub = nil
			sl.NilAcc_Bytes()
		} else {
			o = offsets[lastLayerIdx]
			ub = p.rawPkt[o.start:o.end]
			llStart = o.start
			llEnd = o.end
			sl.SplitRange_Bytes(p.rawPkt, o.start, o.end, writePerm)
		}
	}
	hasHbhLayer := processed[0]
	oHbh := offsets[0]
	ubHbhLayer = hasHbhLayer && !oHbh.isNil ? p.rawPkt[oHbh.start:oHbh.end] : ([]byte)(nil)
	hasE2eLayer := processed[1]
	oE2e := offsets[1]
	ubE2eLayer = hasE2eLayer && !oE2e.isNil ? p.rawPkt[oE2e.start:oE2e.end] : ([]byte)(nil)
	assert processed[0] ==> p.hbhLayer.Mem(ubHbhLayer)
	assert processed[1] ==> p.e2eLayer.Mem(ubE2eLayer)
	@*/
	// @ assert sl.AbsSlice_Bytes(ub, 0, len(ub))
	pld /*@ , start, end @*/ := p.lastLayer.LayerPayload( /*@ ub @*/ )
	// @ sl.SplitRange_Bytes(ub, start, end, writePerm)
	// @ sl.NilAcc_Bytes()

	pathType := /*@ unfolding p.scionLayer.Mem(rawPkt) in @*/ p.scionLayer.PathType
	switch pathType {
	case empty.PathType:
		// @ ghost if mustCombineRanges { ghost defer sl.CombineRange_Bytes(p.rawPkt, o.start, o.end, writePerm) }
		if p.lastLayer.NextLayerType( /*@ ub @*/ ) == layers.LayerTypeBFD {
			// @ ResetDecodingLayers(&p.scionLayer, &p.hbhLayer, &p.e2eLayer, ubScionLayer, ubHbhLayer, ubE2eLayer, true, hasHbhLayer, hasE2eLayer)
			// @ defer fold p.sInit()
			// @ defer fold p.d.validResult(processResult{}, false)
			// @ ghost defer sl.CombineRange_Bytes(ub, start, end, writePerm)
			return processResult{}, p.processIntraBFD(pld) /*@, false @*/
		}
		// @ establishMemUnsupportedPathTypeNextHeader()
		// @ defer fold p.sInit()
		// @ defer fold p.d.validResult(processResult{}, false)
		// @ ghost defer ResetDecodingLayers(&p.scionLayer, &p.hbhLayer, &p.e2eLayer, ubScionLayer, ubHbhLayer, ubE2eLayer, true, hasHbhLayer, hasE2eLayer)
		// @ ghost defer sl.CombineRange_Bytes(ub, start, end, writePerm)
		return processResult{}, serrors.WithCtx(unsupportedPathTypeNextHeader,
			"type", pathType, "header", nextHdr(p.lastLayer /*@, ub @*/)) /*@, false @*/
	case onehop.PathType:
		if p.lastLayer.NextLayerType( /*@ ub @*/ ) == layers.LayerTypeBFD {
			// @ ghost if mustCombineRanges { ghost defer sl.CombineRange_Bytes(p.rawPkt, o.start, o.end, writePerm) }
			// @ ghost defer sl.CombineRange_Bytes(ub, start, end, writePerm)
			// @ unfold acc(p.scionLayer.Mem(p.rawPkt), R10)
			ohp, ok := p.scionLayer.Path.(*onehop.Path)
			// @ fold acc(p.scionLayer.Mem(p.rawPkt), R10)
			if !ok {
				// @ establishMemMalformedPath()
				// @ defer fold p.sInit()
				// @ defer fold p.d.validResult(processResult{}, false)
				// @ ghost defer ResetDecodingLayers(&p.scionLayer, &p.hbhLayer, &p.e2eLayer, ubScionLayer, ubHbhLayer, ubE2eLayer, true, hasHbhLayer, hasE2eLayer)
				return processResult{}, malformedPath /*@, false @*/
			}
			// @ defer fold p.sInit()
			// @ defer fold p.d.validResult(processResult{}, false)
			// @ ghost defer ResetDecodingLayers(&p.scionLayer, &p.hbhLayer, &p.e2eLayer, ubScionLayer, ubHbhLayer, ubE2eLayer, true, hasHbhLayer, hasE2eLayer)
			return processResult{}, p.processInterBFD(ohp, pld) /*@, false @*/
		}
		// @ sl.CombineRange_Bytes(ub, start, end, writePerm)
		// (VerifiedSCION) Nested if because short-circuiting && is not working
		// @ ghost if lastLayerIdx >= 0 {
		// @	if !offsets[lastLayerIdx].isNil {
		// @		o := offsets[lastLayerIdx]
		// @		sl.CombineRange_Bytes(p.rawPkt, o.start, o.end, writePerm)
		// @ 	}
		// @ }
		// @ assert sl.AbsSlice_Bytes(p.rawPkt, 0, len(p.rawPkt))
		// @ unfold acc(p.d.Mem(), _)
		v1, v2 /*@, aliasesPkt @*/ := p.processOHP()
		// @ ResetDecodingLayers(&p.scionLayer, &p.hbhLayer, &p.e2eLayer, ubScionLayer, ubHbhLayer, ubE2eLayer, true, hasHbhLayer, hasE2eLayer)
		// @ fold p.sInit()
		return v1, v2 /*@, aliasesPkt @*/
	case scion.PathType:
		// @ sl.CombineRange_Bytes(ub, start, end, writePerm)
		// (VerifiedSCION) Nested if because short-circuiting && is not working
		// @ ghost if lastLayerIdx >= 0 {
		// @	ghost if !offsets[lastLayerIdx].isNil {
		// @		o := offsets[lastLayerIdx]
		// @		sl.CombineRange_Bytes(p.rawPkt, o.start, o.end, writePerm)
		// @ 	}
		// @ }
		// @ assert sl.AbsSlice_Bytes(p.rawPkt, 0, len(p.rawPkt))
		v1, v2 /*@ , addrAliasesPkt @*/ := p.processSCION( /*@ p.rawPkt, ub == nil, llStart, llEnd @*/ )
		// @ ResetDecodingLayers(&p.scionLayer, &p.hbhLayer, &p.e2eLayer, ubScionLayer, ubHbhLayer, ubE2eLayer, v2 == nil, hasHbhLayer, hasE2eLayer)
		// @ fold p.sInit()
		return v1, v2 /*@, addrAliasesPkt @*/
	case epic.PathType:
		// @ TODO()
		v1, v2 := p.processEPIC()
		// @ fold p.sInit()
		return v1, v2 /*@, false @*/
	default:
		// @ ghost if mustCombineRanges { ghost defer sl.CombineRange_Bytes(p.rawPkt, o.start, o.end, writePerm) }
		// @ ResetDecodingLayers(&p.scionLayer, &p.hbhLayer, &p.e2eLayer, ubScionLayer, ubHbhLayer, ubE2eLayer, true, hasHbhLayer, hasE2eLayer)
		// @ sl.CombineRange_Bytes(ub, start, end, writePerm)
		// @ fold p.d.validResult(processResult{}, false)
		// @ fold p.sInit()
		// @ establishMemUnsupportedPathType()
		return processResult{}, serrors.WithCtx(unsupportedPathType, "type", pathType) /*@, false @*/
	}
}

// @ requires  acc(&p.d, R20)
// @ requires  acc(&p.ingressID, R20)
// @ requires  acc(p.d.Mem(), _)
// @ requires  p.bfdLayer.NonInitMem()
// @ preserves sl.AbsSlice_Bytes(data, 0, len(data))
// @ ensures   acc(&p.d, R20)
// @ ensures   acc(&p.ingressID, R20)
// @ ensures   p.bfdLayer.NonInitMem()
// @ ensures   err != nil ==> err.ErrorMem()
func (p *scionPacketProcessor) processInterBFD(oh *onehop.Path, data []byte) (err error) {
	// @ unfold acc(p.d.Mem(), _)
	// @ ghost if p.d.bfdSessions != nil { unfold acc(accBfdSession(p.d.bfdSessions), _) }
	if len(p.d.bfdSessions) == 0 {
		// @ establishMemNoBFDSessionConfigured()
		return noBFDSessionConfigured
	}

	bfd := &p.bfdLayer
	// @ gopacket.AssertInvariantNilDecodeFeedback()
	if err := bfd.DecodeFromBytes(data, gopacket.NilDecodeFeedback); err != nil {
		return err
	}

	if v, ok := p.d.bfdSessions[p.ingressID]; ok {
		// @ assert v in range(p.d.bfdSessions)
		v.ReceiveMessage(bfd /*@ , data @*/)
		return nil
	}

	// @ bfd.DowngradePerm(data)
	// @ establishMemNoBFDSessionFound()
	return noBFDSessionFound
}

// @ requires  acc(&p.d, R20)
// @ requires  acc(&p.srcAddr, R20) && acc(p.srcAddr.Mem(), _)
// @ requires  p.bfdLayer.NonInitMem()
// @ requires  acc(p.d.Mem(), _)
// @ requires  sl.AbsSlice_Bytes(data, 0, len(data))
// @ ensures   acc(&p.d, R20)
// @ ensures   acc(&p.srcAddr, R20)
// @ ensures   p.bfdLayer.NonInitMem()
// @ ensures   sl.AbsSlice_Bytes(data, 0, len(data))
// @ ensures   res != nil ==> res.ErrorMem()
func (p *scionPacketProcessor) processIntraBFD(data []byte) (res error) {
	// @ unfold acc(p.d.Mem(), _)
	// @ ghost if p.d.bfdSessions != nil { unfold acc(accBfdSession(p.d.bfdSessions), _) }
	if len(p.d.bfdSessions) == 0 {
		// @ establishMemNoBFDSessionConfigured()
		return noBFDSessionConfigured
	}

	bfd := &p.bfdLayer
	// @ gopacket.AssertInvariantNilDecodeFeedback()
	if err := bfd.DecodeFromBytes(data, gopacket.NilDecodeFeedback); err != nil {
		return err
	}

	ifID := uint16(0)
	// @ ghost if p.d.internalNextHops != nil { unfold acc(accAddr(p.d.internalNextHops), _) }

	// (VerifiedSCION) establish ability to use range loop (requires a fixed permission)
	// (VerifiedSCION) TODO: Rewrite this to use regular loop instead to avoid complications with permissions.
	// @ ghost m := p.d.internalNextHops
	// @ assert m != nil ==> acc(m, _)
	// @ inhale m != nil ==> acc(m, R19)

	// @ invariant acc(&p.d, R20/2)
	// @ invariant acc(&p.d.internalNextHops, _)
	// @ invariant m === p.d.internalNextHops
	// @ invariant m != nil ==> acc(m, R20)
	// @ invariant m != nil ==> forall a *net.UDPAddr :: { a in range(m) } a in range(m) ==> acc(a.Mem(), _)
	// @ invariant acc(&p.srcAddr, R20) && acc(p.srcAddr.Mem(), _)
	for k, v := range p.d.internalNextHops /*@ with keys @*/ {
		// @ assert acc(&p.d.internalNextHops, _)
		// @ assert forall a *net.UDPAddr :: { a in range(m) } a in range(m) ==> acc(a.Mem(), _)
		// @ assert acc(v.Mem(), _)
		// @ unfold acc(v.Mem(), _)
		// @ unfold acc(p.srcAddr.Mem(), _)
		if bytes.Equal(v.IP, p.srcAddr.IP) && v.Port == p.srcAddr.Port {
			ifID = k
			break
		}
	}
	// (VerifiedSCION) clean-up code to deal with range loop
	// @ exhale m != nil ==> acc(m, R20)
	// @ inhale m != nil ==> acc(m, _)

	// @ assert acc(&p.d.bfdSessions, _)
	// @ ghost if p.d.bfdSessions != nil { unfold acc(accBfdSession(p.d.bfdSessions), _) }
	if v, ok := p.d.bfdSessions[ifID]; ok {
		// @ assert v in range(p.d.bfdSessions)
		v.ReceiveMessage(bfd /*@ , data @*/)
		return nil
	}

	// @ bfd.DowngradePerm(data)
	// @ establishMemNoBFDSessionFound()
	return noBFDSessionFound
}

// @ requires  0 <= startLL && startLL <= endLL && endLL <= len(ub)
// @ requires  acc(&p.d, R5) && acc(p.d.Mem(), _) && p.d.WellConfigured()
// @ requires  p.d.getValSvc() != nil
// The ghost param ub here allows us to introduce a bound variable to p.rawPkt,
// which slightly simplifies the spec
// @ requires  acc(&p.rawPkt, R1) && ub === p.rawPkt
// @ requires  acc(&p.path)
// @ requires  p.scionLayer.Mem(ub)
// @ requires  sl.AbsSlice_Bytes(ub, 0, len(ub))
// @ preserves acc(&p.srcAddr, R10) && acc(p.srcAddr.Mem(), _)
// @ preserves acc(&p.lastLayer, R10)
// @ preserves p.lastLayer != nil
// @ preserves (p.lastLayer !== &p.scionLayer && llIsNil) ==>
// @ 	acc(p.lastLayer.Mem(nil), R10)
// @ preserves (p.lastLayer !== &p.scionLayer && !llIsNil) ==>
// @ 	acc(p.lastLayer.Mem(ub[startLL:endLL]), R10)
// @ preserves acc(&p.ingressID, R20)
// @ preserves acc(&p.infoField)
// @ preserves acc(&p.hopField)
// @ preserves acc(&p.segmentChange)
// @ preserves acc(&p.mac, R10) && p.mac != nil && p.mac.Mem()
// @ preserves acc(&p.macBuffers.scionInput, R10)
// @ preserves sl.AbsSlice_Bytes(p.macBuffers.scionInput, 0, len(p.macBuffers.scionInput))
// @ preserves acc(&p.cachedMac)
// @ ensures   acc(&p.d, R5)
// @ ensures   acc(&p.path)
// @ ensures   acc(&p.rawPkt, R1)
// @ ensures   reserr == nil ==> p.scionLayer.Mem(ub)
// @ ensures   reserr != nil ==> p.scionLayer.NonInitMem()
// @ ensures   acc(sl.AbsSlice_Bytes(ub, 0, len(ub)), 1 - R15)
// @ ensures   p.d.validResult(respr, addrAliasesPkt)
// @ ensures   addrAliasesPkt ==> (
// @ 	respr.OutAddr != nil &&
// @ 	(acc(respr.OutAddr.Mem(), R15) --* acc(sl.AbsSlice_Bytes(ub, 0, len(ub)), R15)))
// @ ensures   !addrAliasesPkt ==> acc(sl.AbsSlice_Bytes(ub, 0, len(ub)), R15)
// @ ensures   respr.OutPkt !== ub && respr.OutPkt != nil ==>
// @ 	sl.AbsSlice_Bytes(respr.OutPkt, 0, len(respr.OutPkt))
// @ ensures   reserr != nil ==> reserr.ErrorMem()
func (p *scionPacketProcessor) processSCION( /*@ ghost ub []byte, ghost llIsNil bool, ghost startLL int, ghost endLL int @*/ ) (respr processResult, reserr error /*@ , addrAliasesPkt bool @*/) {

	var ok bool
	// @ unfold acc(p.scionLayer.Mem(ub), R20)
	p.path, ok = p.scionLayer.Path.(*scion.Raw)
	// @ fold acc(p.scionLayer.Mem(ub), R20)
	if !ok {
		// TODO(lukedirtwalker) parameter problem invalid path?
		// @ p.scionLayer.DowngradePerm(ub)
		// @ establishMemMalformedPath()
		// @ fold p.d.validResult(processResult{}, false)
		return processResult{}, malformedPath /*@ , false @*/
	}
	return p.process( /*@ ub, llIsNil, startLL, endLL @*/ )
}

// @ trusted
// @ requires false
func (p *scionPacketProcessor) processEPIC() (processResult, error) {

	epicPath, ok := p.scionLayer.Path.(*epic.Path)
	if !ok {
		return processResult{}, malformedPath
	}

	p.path = epicPath.ScionPath
	if p.path == nil {
		return processResult{}, malformedPath
	}

	isPenultimate := p.path.IsPenultimateHop()
	isLast := p.path.IsLastHop()

	result, err := p.process()
	if err != nil {
		return result, err
	}

	if isPenultimate || isLast {
		firstInfo, err := p.path.GetInfoField(0)
		if err != nil {
			return processResult{}, err
		}

		timestamp := time.Unix(int64(firstInfo.Timestamp), 0)
		err = libepic.VerifyTimestamp(timestamp, epicPath.PktID.Timestamp, time.Now())
		if err != nil {
			// TODO(mawyss): Send back SCMP packet
			return processResult{}, err
		}

		HVF := epicPath.PHVF
		if isLast {
			HVF = epicPath.LHVF
		}
		err = libepic.VerifyHVF(p.cachedMac, epicPath.PktID,
			&p.scionLayer, firstInfo.Timestamp, HVF, p.macBuffers.epicInput)
		if err != nil {
			// TODO(mawyss): Send back SCMP packet
			return processResult{}, err
		}
	}

	return result, nil
}

// scionPacketProcessor processes packets. It contains pre-allocated per-packet
// mutable state and context information which should be reused.
type scionPacketProcessor struct {
	// d is a reference to the dataplane instance that initiated this processor.
	d *DataPlane
	// ingressID is the interface ID this packet came in, determined from the
	// socket.
	ingressID uint16
	// rawPkt is the raw packet, it is updated during processing to contain the
	// message to send out.
	rawPkt []byte
	// srcAddr is the source address of the packet
	srcAddr *net.UDPAddr
	// buffer is the buffer that can be used to serialize gopacket layers.
	buffer gopacket.SerializeBuffer
	// mac is the hasher for the MAC computation.
	mac hash.Hash

	// scionLayer is the SCION gopacket layer.
	scionLayer slayers.SCION
	hbhLayer   slayers.HopByHopExtnSkipper
	e2eLayer   slayers.EndToEndExtnSkipper
	// last is the last parsed layer, i.e. either &scionLayer, &hbhLayer or &e2eLayer
	lastLayer gopacket.DecodingLayer

	// path is the raw SCION path. Will be set during processing.
	path *scion.Raw
	// hopField is the current hopField field, is updated during processing.
	hopField path.HopField
	// infoField is the current infoField field, is updated during processing.
	infoField path.InfoField
	// segmentChange indicates if the path segment was changed during processing.
	segmentChange bool

	// cachedMac contains the full 16 bytes of the MAC. Will be set during processing.
	// For a hop performing an Xover, it is the MAC corresponding to the down segment.
	cachedMac []byte
	// macBuffers avoid allocating memory during processing.
	macBuffers macBuffersT

	// bfdLayer is reusable buffer for parsing BFD messages
	bfdLayer layers.BFD
}

// macBuffersT are preallocated buffers for the in- and outputs of MAC functions.
// (VerifiedSCION) This type used to be called macBuffers but this lead to an exception in
// Gobra because there is a field with name and type macBuffers. Because of that, we renamed it.
type macBuffersT struct {
	scionInput []byte
	epicInput  []byte
}

// @ trusted
// @ requires false
func (p *scionPacketProcessor) packSCMP(
	typ slayers.SCMPType,
	code slayers.SCMPCode,
	scmpP gopacket.SerializableLayer,
	cause error,
) (processResult, error) {

	// check invoking packet was an SCMP error:
	if p.lastLayer.NextLayerType() == slayers.LayerTypeSCMP {
		var scmpLayer slayers.SCMP
		err := scmpLayer.DecodeFromBytes(p.lastLayer.LayerPayload(), gopacket.NilDecodeFeedback)
		if err != nil {
			return processResult{}, serrors.WrapStr("decoding SCMP layer", err)
		}
		if !scmpLayer.TypeCode.InfoMsg() {
			return processResult{}, serrors.WrapStr("SCMP error for SCMP error pkt -> DROP", cause)
		}
	}

	rawSCMP, err := p.prepareSCMP(typ, code, scmpP, cause /*@ , nil @*/) // (VerifiedSCION) replace nil by sth else
	return processResult{OutPkt: rawSCMP}, err
}

// @ requires  acc(&p.d, R50) && acc(p.d.Mem(), _)
// @ requires  acc(p.scionLayer.Mem(ub), R5)
// @ requires  acc(&p.path, R20)
// @ requires  p.path === p.scionLayer.GetPath(ub)
// @ requires  acc(&p.hopField) && acc(&p.infoField)
// @ preserves acc(sl.AbsSlice_Bytes(ub, 0, len(ub)), R1)
// @ ensures   acc(&p.d, R50)
// @ ensures   acc(p.scionLayer.Mem(ub), R6)
// @ ensures   acc(&p.path, R20)
// @ ensures   p.path === p.scionLayer.GetPath(ub)
// @ ensures   acc(&p.hopField) && acc(&p.infoField)
// @ ensures   respr === processResult{}
// @ ensures   reserr == nil ==> (
// @	let ubPath := p.scionLayer.UBPath(ub) in
// @	unfolding acc(p.scionLayer.Mem(ub), R10) in
// @	p.path.GetCurrHF(ubPath) < p.path.GetNumHops(ubPath))
// @ ensures   acc(p.scionLayer.Mem(ub), R6)
// @ ensures   p.d.validResult(respr, false)
// @ ensures   reserr == nil ==> (
// @	let ubPath := p.scionLayer.UBPath(ub) in
// @	unfolding acc(p.scionLayer.Mem(ub), R10) in
// @ 	p.path.GetCurrINF(ubPath) < p.path.GetNumINF(ubPath))
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// @ decreases
func (p *scionPacketProcessor) parsePath( /*@ ghost ub []byte @*/ ) (respr processResult, reserr error) {
	var err error
	// @ unfold acc(p.scionLayer.Mem(ub), R6)
	// @ defer fold acc(p.scionLayer.Mem(ub), R6)
	// @ ghost startP := p.scionLayer.PathStartIdx(ub)
	// @ ghost endP := p.scionLayer.PathEndIdx(ub)
	// @ ghost ubPath := ub[startP:endP]
	// @ sl.SplitRange_Bytes(ub, startP, endP, R1)
	// @ ghost defer sl.CombineRange_Bytes(ub, startP, endP, R1)
	p.hopField, err = p.path.GetCurrentHopField( /*@ ubPath @*/ )
	// @ fold p.d.validResult(processResult{}, false)
	if err != nil {
		// TODO(lukedirtwalker) parameter problem invalid path?
		return processResult{}, err
	}
	p.infoField, err = p.path.GetCurrentInfoField( /*@ ubPath @*/ )
	if err != nil {
		// TODO(lukedirtwalker) parameter problem invalid path?
		return processResult{}, err
	}
	return processResult{}, nil
}

// @ preserves acc(&p.infoField, R20)
// @ preserves acc(&p.hopField, R20)
// @ preserves acc(&p.d, R50) && acc(p.d.Mem(), _)
// @ ensures   p.d.validResult(respr, false)
// @ ensures   respr.OutPkt != nil ==>
// @ 	reserr != nil && sl.AbsSlice_Bytes(respr.OutPkt, 0, len(respr.OutPkt))
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// @ decreases
func (p *scionPacketProcessor) validateHopExpiry() (respr processResult, reserr error) {
	expiration := util.SecsToTime(p.infoField.Timestamp).
		Add(path.ExpTimeToDuration(p.hopField.ExpTime))
	expired := expiration.Before(time.Now())
	if !expired {
		// @ fold p.d.validResult(respr, false)
		return processResult{}, nil
	}
	// @ TODO()
	// TODO: adapt; note that packSCMP always returns an empty addr and conn and
	// when the err is nil, it returns the bytes of p.buffer. This should be a magic wand
	// that is consumed after sending the reply. For now, we are making this simplifying
	// assumption, but in the future, we should elaborate the proof for this to not be
	// necessary. To do this, we need to return a flag everywhere that says whether the
	// pkt overlaps with p.buffer and, if so, a wand from AbsSlice of its underlying slice
	// to p.buffer.Mem(). This is very similar to what we did with the address.
	// The flag would be added to processPkt, processSCION, process. Only when processing
	// SCION could this flag be true. In all other cases, it will be false. The processResult
	// that is returned never overlaps with the rawPkt
	return p.packSCMP(
		slayers.SCMPTypeParameterProblem,
		slayers.SCMPCodePathExpired,
		&slayers.SCMPParameterProblem{Pointer: p.currentHopPointer( /*@ nil @*/ )},
		serrors.New("expired hop", "cons_dir", p.infoField.ConsDir, "if_id", p.ingressID,
			"curr_inf", p.path.PathMeta.CurrINF, "curr_hf", p.path.PathMeta.CurrHF),
	)
}

// @ preserves acc(&p.infoField, R20)
// @ preserves acc(&p.hopField, R20)
// @ preserves acc(&p.ingressID, R20)
// @ preserves acc(&p.d, R50) && acc(p.d.Mem(), _)
// @ ensures   p.d.validResult(respr, false)
// @ ensures   respr.OutPkt != nil ==> reserr != nil && sl.AbsSlice_Bytes(respr.OutPkt, 0, len(respr.OutPkt))
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// @ ensures   reserr == nil && p.infoField.ConsDir ==> (
// @ 	p.ingressID == 0 || p.hopField.ConsIngress == p.ingressID)
// @ ensures   reserr == nil && !p.infoField.ConsDir ==> (
// @ 	p.ingressID == 0 || p.hopField.ConsEgress == p.ingressID)
// @ decreases
func (p *scionPacketProcessor) validateIngressID() (respr processResult, reserr error) {
	pktIngressID := p.hopField.ConsIngress
	errCode := slayers.SCMPCodeUnknownHopFieldIngress
	if !p.infoField.ConsDir {
		pktIngressID = p.hopField.ConsEgress
		errCode = slayers.SCMPCodeUnknownHopFieldEgress
	}
	if p.ingressID != 0 && p.ingressID != pktIngressID {
		// @ TODO()
		return p.packSCMP(
			slayers.SCMPTypeParameterProblem,
			errCode,
			&slayers.SCMPParameterProblem{Pointer: p.currentHopPointer( /*@ nil @*/ )},
			serrors.New("ingress interface invalid",
				"pkt_ingress", pktIngressID, "router_ingress", p.ingressID),
		)
	}
	// @ fold p.d.validResult(respr, false)
	return processResult{}, nil
}

// @ requires  acc(&p.d, R20) && acc(p.d.Mem(), _)
// @ requires  acc(p.scionLayer.Mem(ubScionL), R19)
// @ requires  acc(&p.path, R20)
// @ requires  p.path === p.scionLayer.GetPath(ubScionL)
// @ preserves acc(&p.ingressID, R20)
// @ ensures   acc(p.scionLayer.Mem(ubScionL), R19)
// @ ensures   acc(&p.path, R20)
// @ ensures   acc(&p.d, R20)
// @ ensures   p.d.validResult(respr, false)
// @ ensures   respr.OutPkt != nil ==>
// @ 	reserr != nil && sl.AbsSlice_Bytes(respr.OutPkt, 0, len(respr.OutPkt))
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// @ decreases
func (p *scionPacketProcessor) validateSrcDstIA( /*@ ghost ubScionL []byte @*/ ) (respr processResult, reserr error) {
	// @ ghost ubPath := p.scionLayer.UBPath(ubScionL)
	// @ unfold acc(p.scionLayer.Mem(ubScionL), R20)
	// @ defer fold acc(p.scionLayer.Mem(ubScionL), R20)
	// @ unfold acc(p.scionLayer.HeaderMem(ubScionL[slayers.CmnHdrLen:]), R20)
	// @ defer fold acc(p.scionLayer.HeaderMem(ubScionL[slayers.CmnHdrLen:]), R20)
	// @ p.d.getLocalIA()
	srcIsLocal := (p.scionLayer.SrcIA == p.d.localIA)
	dstIsLocal := (p.scionLayer.DstIA == p.d.localIA)
	if p.ingressID == 0 {
		// Outbound
		// Only check SrcIA if first hop, for transit this already checked by ingress router.
		// Note: SCMP error messages triggered by the sibling router may use paths that
		// don't start with the first hop.
		if p.path.IsFirstHop( /*@ ubPath @*/ ) && !srcIsLocal {
			// @ TODO() // depends on packSCMP
			return p.invalidSrcIA()
		}
		if dstIsLocal {
			// @ TODO() // depends on packSCMP
			return p.invalidDstIA()
		}
	} else {
		// Inbound
		if srcIsLocal {
			// @ TODO() // depends on packSCMP
			return p.invalidSrcIA()
		}
		if p.path.IsLastHop( /*@ ubPath @*/ ) != dstIsLocal {
			// @ TODO() // depends on packSCMP
			return p.invalidDstIA()
		}
	}
	// @ fold p.d.validResult(processResult{}, false)
	return processResult{}, nil
}

// invalidSrcIA is a helper to return an SCMP error for an invalid SrcIA.
// @ trusted
// @ requires false
func (p *scionPacketProcessor) invalidSrcIA() (processResult, error) {
	return p.packSCMP(
		slayers.SCMPTypeParameterProblem,
		slayers.SCMPCodeInvalidSourceAddress,
		&slayers.SCMPParameterProblem{Pointer: uint16(slayers.CmnHdrLen + addr.IABytes)},
		invalidSrcIA,
	)
}

// invalidDstIA is a helper to return an SCMP error for an invalid DstIA.
// @ trusted
// @ requires false
func (p *scionPacketProcessor) invalidDstIA() (processResult, error) {
	return p.packSCMP(
		slayers.SCMPTypeParameterProblem,
		slayers.SCMPCodeInvalidDestinationAddress,
		&slayers.SCMPParameterProblem{Pointer: uint16(slayers.CmnHdrLen)},
		invalidDstIA,
	)
}

// validateTransitUnderlaySrc checks that the source address of transit packets
// matches the expected sibling router.
// Provided that underlying network infrastructure prevents address spoofing,
// this check prevents malicious end hosts in the local AS from bypassing the
// SrcIA checks by disguising packets as transit traffic.
// @ requires  acc(&p.path, R15)
// @ requires  acc(p.scionLayer.Mem(ub), R4)
// @ requires  p.path === p.scionLayer.GetPath(ub)
// @ requires  acc(&p.ingressID, R20)
// @ requires  acc(&p.infoField, R4) && acc(&p.hopField, R4)
// @ requires  let ubPath := p.scionLayer.UBPath(ub) in
// @	unfolding acc(p.scionLayer.Mem(ub), R10) in
// @	p.path.GetCurrHF(ubPath) <= p.path.GetNumHops(ubPath)
// @ requires  let ubPath := p.scionLayer.UBPath(ub) in
// @	unfolding acc(p.scionLayer.Mem(ub), R10) in
// @	p.path.GetCurrINF(ubPath) <= p.path.GetNumINF(ubPath)
// @ requires  acc(&p.d, R20) && acc(p.d.Mem(), _)
// @ requires  acc(&p.srcAddr, R20) && acc(p.srcAddr.Mem(), _)
// @ preserves acc(sl.AbsSlice_Bytes(ub, 0, len(ub)), R4)
// @ ensures   acc(&p.path, R15)
// @ ensures   acc(p.scionLayer.Mem(ub), R4)
// @ ensures   acc(&p.ingressID, R20)
// @ ensures   acc(&p.infoField, R4) && acc(&p.hopField, R4)
// @ ensures   acc(&p.d, R20)
// @ ensures   acc(&p.srcAddr, R20)
// @ ensures   p.d.validResult(respr, false)
// @ ensures   respr.OutPkt == nil
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// @ decreases
func (p *scionPacketProcessor) validateTransitUnderlaySrc( /*@ ghost ub []byte @*/ ) (respr processResult, reserr error) {
	// @ ghost startP := p.scionLayer.PathStartIdx(ub)
	// @ ghost endP := p.scionLayer.PathEndIdx(ub)
	// @ unfold acc(p.scionLayer.Mem(ub), R4)
	// @ defer fold acc(p.scionLayer.Mem(ub), R4)
	// @ ghost ubPath := ub[startP:endP]
	// @ sl.SplitRange_Bytes(ub, startP, endP, R5)
	// @ ghost defer sl.CombineRange_Bytes(ub, startP, endP, R5)
	// (VerifiedSCION) Gobra cannot prove this property yet, even though it follows
	// from the type system
	// @ assume 0 <= p.path.GetCurrHF(ubPath) // TODO: drop assumptions like this
	if p.path.IsFirstHop( /*@ ubPath @*/ ) || p.ingressID != 0 {
		// not a transit packet, nothing to check
		// @ fold p.d.validResult(processResult{}, false)
		return processResult{}, nil
	}
	pktIngressID := p.ingressInterface( /*@ ubPath @*/ )
	// @ p.d.getInternalNextHops()
	// @ ghost if p.d.internalNextHops != nil { unfold acc(accAddr(p.d.internalNextHops), _) }
	expectedSrc, ok := p.d.internalNextHops[pktIngressID]
	// @ ghost if ok {
	// @	assert expectedSrc in range(p.d.internalNextHops)
	// @    unfold acc(expectedSrc.Mem(), _)
	// @ }
	// @ unfold acc(p.srcAddr.Mem(), _)
	if !ok || !expectedSrc.IP.Equal(p.srcAddr.IP) {
		// Drop
		// @ establishInvalidSrcAddrForTransit()
		// @ fold p.d.validResult(processResult{}, false)
		return processResult{}, invalidSrcAddrForTransit
	}
	// @ fold p.d.validResult(processResult{}, false)
	return processResult{}, nil
}

// @ requires  acc(&p.d, R20) && acc(p.d.Mem(), _)
// @ preserves acc(&p.ingressID, R20)
// @ preserves acc(&p.segmentChange, R20)
// @ preserves acc(&p.infoField, R20)
// @ preserves acc(&p.hopField, R20)
// @ ensures   acc(&p.d, R20)
// @ ensures   p.d.validResult(respr, false)
// @ ensures   reserr == nil ==> respr === processResult{}
// @ ensures   reserr != nil ==> sl.AbsSlice_Bytes(respr.OutPkt, 0, len(respr.OutPkt))
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// @ decreases
func (p *scionPacketProcessor) validateEgressID() (respr processResult, reserr error) {
	pktEgressID := p.egressInterface()
	// @ p.d.getInternalNextHops()
	// @ if p.d.internalNextHops != nil { unfold acc(accAddr(p.d.internalNextHops), _) }
	_, ih := p.d.internalNextHops[pktEgressID]
	// @ p.d.getExternalMem()
	// @ if p.d.external != nil { unfold acc(accBatchConn(p.d.external), _) }
	_, eh := p.d.external[pktEgressID]
	if !ih && !eh {
		errCode := slayers.SCMPCodeUnknownHopFieldEgress
		if !p.infoField.ConsDir {
			errCode = slayers.SCMPCodeUnknownHopFieldIngress
		}
		// @ TODO()
		return p.packSCMP(
			slayers.SCMPTypeParameterProblem,
			errCode,
			&slayers.SCMPParameterProblem{Pointer: p.currentHopPointer( /*@ nil @*/ )},
			cannotRoute,
		)
	}

	// @ p.d.getLinkTypesMem()
	ingress, egress := p.d.linkTypes[p.ingressID], p.d.linkTypes[pktEgressID]
	if !p.segmentChange {
		// Check that the interface pair is valid within a single segment.
		// No check required if the packet is received from an internal interface.
		switch {
		case p.ingressID == 0:
			// @ fold p.d.validResult(respr, false)
			return processResult{}, nil
		case ingress == topology.Core && egress == topology.Core:
			// @ fold p.d.validResult(respr, false)
			return processResult{}, nil
		case ingress == topology.Child && egress == topology.Parent:
			// @ fold p.d.validResult(respr, false)
			return processResult{}, nil
		case ingress == topology.Parent && egress == topology.Child:
			// @ fold p.d.validResult(respr, false)
			return processResult{}, nil
		default: // malicious
			// @ TODO()
			return p.packSCMP(
				slayers.SCMPTypeParameterProblem,
				slayers.SCMPCodeInvalidPath, // XXX(matzf) new code InvalidHop?
				&slayers.SCMPParameterProblem{Pointer: p.currentHopPointer( /*@ nil @*/ )},
				serrors.WithCtx(cannotRoute, "ingress_id", p.ingressID, "ingress_type", ingress,
					"egress_id", pktEgressID, "egress_type", egress))
		}
	}
	// Check that the interface pair is valid on a segment switch.
	// Having a segment change received from the internal interface is never valid.
	switch {
	case ingress == topology.Core && egress == topology.Child:
		// @ fold p.d.validResult(respr, false)
		return processResult{}, nil
	case ingress == topology.Child && egress == topology.Core:
		// @ fold p.d.validResult(respr, false)
		return processResult{}, nil
	case ingress == topology.Child && egress == topology.Child:
		// @ fold p.d.validResult(respr, false)
		return processResult{}, nil
	default:
		// @ TODO()
		return p.packSCMP(
			slayers.SCMPTypeParameterProblem,
			slayers.SCMPCodeInvalidSegmentChange,
			&slayers.SCMPParameterProblem{Pointer: p.currentInfoPointer( /*@ nil @*/ )},
			serrors.WithCtx(cannotRoute, "ingress_id", p.ingressID, "ingress_type", ingress,
				"egress_id", pktEgressID, "egress_type", egress))
	}
}

// @ preserves acc(&p.infoField)
// @ requires  acc(&p.path, R20)
// @ requires  acc(p.scionLayer.Mem(ub), R19)
// @ requires  p.path === p.scionLayer.GetPath(ub)
// @ preserves acc(&p.ingressID, R20)
// @ preserves acc(&p.hopField,  R20)
// @ preserves sl.AbsSlice_Bytes(ub, 0, len(ub))
// @ ensures   acc(&p.path, R20)
// @ ensures   acc(p.scionLayer.Mem(ub), R19)
// @ ensures   err != nil ==> err.ErrorMem()
// @ decreases
func (p *scionPacketProcessor) updateNonConsDirIngressSegID( /*@ ghost ub []byte @*/ ) (err error) {
	// @ ghost ubPath := p.scionLayer.UBPath(ub)
	// @ ghost start := p.scionLayer.PathStartIdx(ub)
	// @ ghost end   := p.scionLayer.PathEndIdx(ub)
	// @ assert ub[start:end] === ubPath

	// @ unfold acc(p.scionLayer.Mem(ub), R20)
	// @ defer fold acc(p.scionLayer.Mem(ub), R20)
	// against construction dir the ingress router updates the SegID, ifID == 0
	// means this comes from this AS itself, so nothing has to be done.
	// TODO(lukedirtwalker): For packets destined to peer links this shouldn't
	// be updated.
	if !p.infoField.ConsDir && p.ingressID != 0 {
		p.infoField.UpdateSegID(p.hopField.Mac)
		// (VerifiedSCION) the following property is guaranteed by the type system, but Gobra cannot infer it yet
		// @ assume 0 <= p.path.GetCurrINF(ubPath)
		// @ sl.SplitRange_Bytes(ub, start, end, writePerm)
		// @ ghost defer sl.CombineRange_Bytes(ub, start, end, writePerm)
		if err := p.path.SetInfoField(p.infoField, int( /*@ unfolding acc(p.path.Mem(ubPath), R45) in (unfolding acc(p.path.Base.Mem(), R50) in @*/ p.path.PathMeta.CurrINF) /*@ ) , ubPath @*/); err != nil {
			return serrors.WrapStr("update info field", err)
		}
	}
	return nil
}

// @ requires acc(p.scionLayer.Mem(ubScionL), R20)
// @ requires acc(&p.path, R20)
// @ requires p.path == p.scionLayer.GetPath(ubScionL)
// @ ensures  acc(p.scionLayer.Mem(ubScionL), R20)
// @ ensures  acc(&p.path, R20)
// @ decreases
func (p *scionPacketProcessor) currentInfoPointer( /*@ ghost ubScionL []byte @*/ ) uint16 {
	// @ ghost ubPath := p.scionLayer.UBPath(ubScionL)
	// @ unfold acc(p.scionLayer.Mem(ubScionL), R21)
	// @ defer  fold acc(p.scionLayer.Mem(ubScionL), R21)
	// @ unfold acc(p.scionLayer.Path.Mem(ubPath), R21)
	// @ defer  fold acc(p.scionLayer.Path.Mem(ubPath), R21)
	// @ unfold acc(p.scionLayer.Path.(*scion.Raw).Base.Mem(), R21)
	// @ defer  fold acc(p.scionLayer.Path.(*scion.Raw).Base.Mem(), R21)
	return uint16(slayers.CmnHdrLen + p.scionLayer.AddrHdrLen( /*@ ubScionL, false @*/ ) +
		scion.MetaLen + path.InfoLen*int(p.path.PathMeta.CurrINF))
}

// (VerifiedSCION) This could probably be made pure, but it is likely not beneficial, nor needed
// to expose the body of this function at the moment.
// @ requires acc(p.scionLayer.Mem(ubScionL), R20)
// @ requires acc(&p.path, R20)
// @ requires p.path == p.scionLayer.GetPath(ubScionL)
// @ ensures  acc(p.scionLayer.Mem(ubScionL), R20)
// @ ensures  acc(&p.path, R20)
// @ decreases
func (p *scionPacketProcessor) currentHopPointer( /*@ ghost ubScionL []byte @*/ ) uint16 {
	// @ ghost ubPath := p.scionLayer.UBPath(ubScionL)
	// @ unfold acc(p.scionLayer.Mem(ubScionL), R20/2)
	// @ defer  fold acc(p.scionLayer.Mem(ubScionL), R20/2)
	// @ unfold acc(p.scionLayer.Path.Mem(ubPath), R20/2)
	// @ defer  fold acc(p.scionLayer.Path.Mem(ubPath), R20/2)
	// @ unfold acc(p.scionLayer.Path.(*scion.Raw).Base.Mem(), R20/2)
	// @ defer  fold acc(p.scionLayer.Path.(*scion.Raw).Base.Mem(), R20/2)
	return uint16(slayers.CmnHdrLen + p.scionLayer.AddrHdrLen( /*@ ubScionL, false @*/ ) +
		scion.MetaLen + path.InfoLen*p.path.NumINF + path.HopLen*int(p.path.PathMeta.CurrHF))
}

// @ preserves acc(&p.mac, R20) && p.mac != nil && p.mac.Mem()
// @ preserves acc(&p.infoField, R20)
// @ preserves acc(&p.hopField,  R20)
// @ preserves acc(&p.macBuffers.scionInput, R20)
// @ preserves sl.AbsSlice_Bytes(p.macBuffers.scionInput, 0, len(p.macBuffers.scionInput))
// @ preserves acc(&p.cachedMac)
// @ preserves acc(&p.d, R50) && acc(p.d.Mem(), _)
// @ ensures   p.d.validResult(respr, false)
// @ ensures   respr.OutPkt != nil ==>
// @ 	reserr != nil && sl.AbsSlice_Bytes(respr.OutPkt, 0, len(respr.OutPkt))
// @ ensures   len(p.cachedMac) == path.MACBufferSize
// @ ensures   sl.AbsSlice_Bytes(p.cachedMac, 0, len(p.cachedMac))
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// @ decreases
func (p *scionPacketProcessor) verifyCurrentMAC() (respr processResult, reserr error) {
	fullMac := path.FullMAC(p.mac, p.infoField, p.hopField, p.macBuffers.scionInput)
	// @ fold acc(sl.AbsSlice_Bytes(p.hopField.Mac[:path.MacLen], 0, path.MacLen), R20)
	// @ defer unfold acc(sl.AbsSlice_Bytes(p.hopField.Mac[:path.MacLen], 0, path.MacLen), R20)
	// @ sl.SplitRange_Bytes(fullMac, 0, path.MacLen, R20)
	// @ ghost defer sl.CombineRange_Bytes(fullMac, 0, path.MacLen, R20)
	if subtle.ConstantTimeCompare(p.hopField.Mac[:path.MacLen], fullMac[:path.MacLen]) == 0 {
		// @ TODO()
		return p.packSCMP(
			slayers.SCMPTypeParameterProblem,
			slayers.SCMPCodeInvalidHopFieldMAC,
			&slayers.SCMPParameterProblem{Pointer: p.currentHopPointer( /*@ nil @*/ )},
			serrors.New("MAC verification failed", "expected", fmt.Sprintf(
				"%x", fullMac[:path.MacLen]),
				"actual", fmt.Sprintf("%x", p.hopField.Mac[:path.MacLen]),
				"cons_dir", p.infoField.ConsDir,
				"if_id", p.ingressID, "curr_inf", p.path.PathMeta.CurrINF,
				"curr_hf", p.path.PathMeta.CurrHF, "seg_id", p.infoField.SegID),
		)
	}
	// Add the full MAC to the SCION packet processor,
	// such that EPIC does not need to recalculate it.
	p.cachedMac = fullMac

	// @ fold p.d.validResult(processResult{}, false)
	return processResult{}, nil
}

// @ requires  acc(&p.d, R15)
// @ requires  acc(p.d.Mem(), _)
// @ requires  p.d.getValSvc() != nil
// @ requires  acc(sl.AbsSlice_Bytes(ubScionL, 0, len(ubScionL)), R15)
// @ preserves acc(p.scionLayer.Mem(ubScionL), R10)
// @ ensures   acc(&p.d, R15)
// @ ensures   p.d.validResult(respr, addrAliasesUb)
// @ ensures   !addrAliasesUb ==> acc(sl.AbsSlice_Bytes(ubScionL, 0, len(ubScionL)), R15)
// @ ensures   !addrAliasesUb && resaddr != nil ==> acc(resaddr.Mem(), _)
// @ ensures   addrAliasesUb ==> resaddr != nil
// @ ensures   addrAliasesUb ==> acc(resaddr.Mem(), R15)
// @ ensures   addrAliasesUb ==> (acc(resaddr.Mem(), R15) --* acc(sl.AbsSlice_Bytes(ubScionL, 0, len(ubScionL)), R15))
// @ ensures   respr.OutPkt != nil ==>
// @ 	reserr != nil && sl.AbsSlice_Bytes(respr.OutPkt, 0, len(respr.OutPkt))
// @ ensures   reserr != nil ==> !addrAliasesUb
// @ ensures   reserr != nil ==> reserr.ErrorMem()
func (p *scionPacketProcessor) resolveInbound( /*@ ghost ubScionL []byte @*/ ) (resaddr *net.UDPAddr, respr processResult, reserr error /*@ , addrAliasesUb bool @*/) {
	// (VerifiedSCION) the parameter used to be p.scionLayer,
	// instead of &p.scionLayer.
	a, err /*@ , addrAliases @*/ := p.d.resolveLocalDst(&p.scionLayer /*@, ubScionL @*/)
	// @ establishNoSVCBackend()
	switch {
	case errors.Is(err, noSVCBackend):
		// @ ghost if addrAliases {
		// @ 	apply acc(a.Mem(), R15) --* acc(sl.AbsSlice_Bytes(ubScionL, 0, len(ubScionL)), R15)
		// @ }
		// @ TODO()
		r, err := p.packSCMP(
			slayers.SCMPTypeDestinationUnreachable,
			slayers.SCMPCodeNoRoute,
			&slayers.SCMPDestinationUnreachable{}, err)
		return nil, r, err /*@ , false @*/
	default:
		// @ fold p.d.validResult(respr, addrAliases)
		return a, processResult{}, nil /*@ , addrAliases @*/
	}
}

// @ requires  acc(&p.path, R20)
// @ requires  p.scionLayer.Mem(ub)
// @ requires  p.path === p.scionLayer.GetPath(ub)
// @ preserves acc(&p.infoField)
// @ preserves acc(&p.hopField, R20)
// @ preserves sl.AbsSlice_Bytes(ub, 0, len(ub))
// @ ensures   acc(&p.path, R20)
// @ ensures   reserr == nil ==> p.scionLayer.Mem(ub)
// @ ensures   reserr != nil ==> p.scionLayer.NonInitMem()
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// @ decreases
func (p *scionPacketProcessor) processEgress( /*@ ghost ub []byte @*/ ) (reserr error) {
	// @ ghost ubPath := p.scionLayer.UBPath(ub)
	// @ ghost startP := p.scionLayer.PathStartIdx(ub)
	// @ ghost endP   := p.scionLayer.PathEndIdx(ub)
	// @ assert ub[startP:endP] === ubPath

	// @ unfold p.scionLayer.Mem(ub)
	// @ sl.SplitRange_Bytes(ub, startP, endP, writePerm)
	// @ ghost defer sl.CombineRange_Bytes(ub, startP, endP, writePerm)
	// we are the egress router and if we go in construction direction we
	// need to update the SegID.
	if p.infoField.ConsDir {
		p.infoField.UpdateSegID(p.hopField.Mac)
		// @ assume 0 <= p.path.GetCurrINF(ubPath)
		if err := p.path.SetInfoField(p.infoField, int( /*@ unfolding acc(p.path.Mem(ubPath), R45) in (unfolding acc(p.path.Base.Mem(), R50) in @*/ p.path.PathMeta.CurrINF /*@ ) @*/) /*@ , ubPath @*/); err != nil {
			// TODO parameter problem invalid path
			// @ p.path.DowngradePerm(ubPath)
			// @ p.scionLayer.PathPoolMemExchange(p.scionLayer.PathType, p.scionLayer.Path)
			// @ unfold p.scionLayer.HeaderMem(ub[slayers.CmnHdrLen:])
			// @ fold p.scionLayer.NonInitMem()
			return serrors.WrapStr("update info field", err)
		}
	}
	if err := p.path.IncPath( /*@ ubPath @*/ ); err != nil {
		// @ p.scionLayer.PathPoolMemExchange(p.scionLayer.PathType, p.scionLayer.Path)
		// @ unfold p.scionLayer.HeaderMem(ub[slayers.CmnHdrLen:])
		// @ fold p.scionLayer.NonInitMem()
		// TODO parameter problem invalid path
		return serrors.WrapStr("incrementing path", err)
	}
	// @ fold p.scionLayer.Mem(ub)
	return nil
}

// @ requires  acc(&p.path, R20)
// @ requires  p.scionLayer.Mem(ub)
// @ requires  p.path == p.scionLayer.GetPath(ub)
// @ preserves acc(&p.segmentChange) && acc(&p.hopField) && acc(&p.infoField)
// @ preserves sl.AbsSlice_Bytes(ub, 0, len(ub))
// @ ensures   acc(&p.path, R20)
// @ ensures   reserr == nil ==> (p.scionLayer.Mem(ub) && p.scionLayer.UBPath(ub) === old(p.scionLayer.UBPath(ub)) && p.scionLayer.GetPath(ub) === old(p.scionLayer.GetPath(ub)))
// @ ensures   reserr != nil ==> p.scionLayer.NonInitMem()
// @ ensures   p.segmentChange
// @ ensures   respr === processResult{}
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// @ decreases
func (p *scionPacketProcessor) doXover( /*@ ghost ub []byte @*/ ) (respr processResult, reserr error) {
	p.segmentChange = true
	// @ unfold p.scionLayer.Mem(ub)
	// @ ghost  startP := int(slayers.CmnHdrLen + p.scionLayer.AddrHdrLen(nil, true))
	// @ ghost  endP   := int(p.scionLayer.HdrLen * slayers.LineLen)
	// @ ghost  ubPath := ub[startP:endP]
	// @ sl.SplitRange_Bytes(ub, startP, endP, writePerm)
	// @ ghost defer sl.CombineRange_Bytes(ub, startP, endP, writePerm)
	if err := p.path.IncPath( /*@ ubPath @*/ ); err != nil {
		// TODO parameter problem invalid path
		// TODO(joao): we currently expose a lot of internal information from slayers here. Can we avoid it?
		// @ unfold p.scionLayer.HeaderMem(ub[slayers.CmnHdrLen:])
		// @ p.scionLayer.PathPoolMemExchange(p.scionLayer.PathType, p.scionLayer.Path)
		// @ fold p.scionLayer.NonInitMem()
		return processResult{}, serrors.WrapStr("incrementing path", err)
	}
	var err error
	if p.hopField, err = p.path.GetCurrentHopField( /*@ ubPath @*/ ); err != nil {
		// @ fold p.scionLayer.Mem(ub)
		// @ p.scionLayer.DowngradePerm(ub)
		// TODO parameter problem invalid path
		return processResult{}, err
	}
	if p.infoField, err = p.path.GetCurrentInfoField( /*@ ubPath @*/ ); err != nil {
		// @ fold p.scionLayer.Mem(ub)
		// @ p.scionLayer.DowngradePerm(ub)
		// TODO parameter problem invalid path
		return processResult{}, err
	}
	// @ fold p.scionLayer.Mem(ub)
	return processResult{}, nil
}

// @ requires  acc(&p.path, R20)
// @ requires  acc(p.path.Mem(ubPath), R5)
// @ requires  acc(&p.infoField, R5) && acc(&p.hopField, R5)
// @ requires  p.path.GetCurrINF(ubPath) <= p.path.GetNumINF(ubPath)
// @ requires  p.path.GetCurrHF(ubPath) <= p.path.GetNumHops(ubPath)
// @ preserves acc(sl.AbsSlice_Bytes(ubPath, 0, len(ubPath)), R5)
// @ ensures   acc(&p.path, R20)
// @ ensures   acc(p.path.Mem(ubPath), R5)
// @ ensures   acc(&p.infoField, R5) && acc(&p.hopField, R5)
// @ decreases
func (p *scionPacketProcessor) ingressInterface( /*@ ghost ubPath []byte @*/ ) uint16 {
	info := p.infoField
	hop := p.hopField
	if p.path.IsFirstHopAfterXover( /*@ ubPath @*/ ) {
		var err error
		info, err = p.path.GetInfoField(int( /*@ unfolding acc(p.path.Mem(ubPath), R45) in (unfolding acc(p.path.Base.Mem(), R50) in @*/ p.path.PathMeta.CurrINF /*@ ) @*/) - 1 /*@ , ubPath @*/)
		if err != nil { // cannot be out of range
			panic(err)
		}
		hop, err = p.path.GetHopField(int( /*@ unfolding acc(p.path.Mem(ubPath), R45) in (unfolding acc(p.path.Base.Mem(), R50) in @*/ p.path.PathMeta.CurrHF /*@ ) @*/) - 1 /*@ , ubPath @*/)
		if err != nil { // cannot be out of range
			panic(err)
		}
	}
	if info.ConsDir {
		return hop.ConsIngress
	}
	return hop.ConsEgress
}

// @ preserves acc(&p.infoField, R20)
// @ preserves acc(&p.hopField, R20)
// @ decreases
func (p *scionPacketProcessor) egressInterface() uint16 {
	if p.infoField.ConsDir {
		return p.hopField.ConsEgress
	}
	return p.hopField.ConsIngress
}

// @ requires  acc(&p.d, R20) && acc(p.d.Mem(), _)
// @ preserves acc(&p.infoField, R20)
// @ preserves acc(&p.hopField, R20)
// @ preserves acc(&p.ingressID, R20)
// @ ensures   acc(&p.d, R20)
// @ ensures   p.d.validResult(respr, false)
// @ ensures   respr.OutPkt != nil ==>
// @ 	reserr != nil && sl.AbsSlice_Bytes(respr.OutPkt, 0, len(respr.OutPkt))
// @ ensures   reserr != nil ==> reserr.ErrorMem()
func (p *scionPacketProcessor) validateEgressUp() (respr processResult, reserr error) {
	egressID := p.egressInterface()
	// @ p.d.getBfdSessionsMem()
	// @ ghost if p.d.bfdSessions != nil { unfold acc(accBfdSession(p.d.bfdSessions), _) }
	if v, ok := p.d.bfdSessions[egressID]; ok {
		if !v.IsUp() {
			typ := slayers.SCMPTypeExternalInterfaceDown
			// @ p.d.getLocalIA()
			var scmpP gopacket.SerializableLayer = &slayers.SCMPExternalInterfaceDown{
				IA:   p.d.localIA,
				IfID: uint64(egressID),
			}
			// @ p.d.getExternalMem()
			// @ if p.d.external != nil { unfold acc(accBatchConn(p.d.external), _) }
			if _, external := p.d.external[egressID]; !external {
				typ = slayers.SCMPTypeInternalConnectivityDown
				scmpP = &slayers.SCMPInternalConnectivityDown{
					IA:      p.d.localIA,
					Ingress: uint64(p.ingressID),
					Egress:  uint64(egressID),
				}
			}
			// @ TODO()
			return p.packSCMP(typ, 0, scmpP, serrors.New("bfd session down"))
		}
	}
	// @ fold p.d.validResult(processResult{}, false)
	return processResult{}, nil
}

// @ requires  0 <= startLL && startLL <= endLL && endLL <= len(ub)
// @ requires  acc(&p.path, R20)
// @ requires  acc(p.scionLayer.Mem(ub), R10)
// @ requires  p.path === p.scionLayer.GetPath(ub)
// @ requires  acc(&p.d, R20) && acc(p.d.Mem(), _)
// @ preserves sl.AbsSlice_Bytes(ub, 0, len(ub))
// @ preserves acc(&p.lastLayer, R19)
// @ preserves p.lastLayer != nil
// @ preserves (&p.scionLayer !== p.lastLayer && llIsNil) ==>
// @ 	acc(p.lastLayer.Mem(nil), R15)
// @ preserves (&p.scionLayer !== p.lastLayer && !llIsNil) ==>
// @ 	acc(p.lastLayer.Mem(ub[startLL:endLL]), R15)
// @ preserves acc(&p.ingressID, R20)
// @ preserves acc(&p.infoField, R20)
// @ preserves acc(&p.hopField)
// @ ensures   acc(&p.path, R20)
// @ ensures   acc(p.scionLayer.Mem(ub), R10)
// @ ensures   acc(&p.d, R20)
// @ ensures   p.d.validResult(respr, false)
// @ ensures   respr.OutPkt != nil ==>
// @ 	reserr != nil && sl.AbsSlice_Bytes(respr.OutPkt, 0, len(respr.OutPkt))
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// @ decreases
func (p *scionPacketProcessor) handleIngressRouterAlert( /*@ ghost ub []byte, ghost llIsNil bool, ghost startLL int, ghost endLL int @*/ ) (respr processResult, reserr error) {
	// @ ghost ubPath := p.scionLayer.UBPath(ub)
	// @ ghost startP := p.scionLayer.PathStartIdx(ub)
	// @ ghost endP   := p.scionLayer.PathEndIdx(ub)
	// @ assert ub[startP:endP] === ubPath
	if p.ingressID == 0 {
		// @ fold p.d.validResult(processResult{}, false)
		return processResult{}, nil
	}
	alert := p.ingressRouterAlertFlag()
	if !*alert {
		// @ fold p.d.validResult(processResult{}, false)
		return processResult{}, nil
	}
	*alert = false
	// @ unfold acc(p.scionLayer.Mem(ub), R20)
	// @ defer fold acc(p.scionLayer.Mem(ub), R20)
	// (VerifiedSCION) the following is guaranteed by the type system, but Gobra cannot prove it yet
	// @ assume 0 <= p.path.GetCurrHF(ubPath)
	// @ sl.SplitRange_Bytes(ub, startP, endP, writePerm)
	if err := p.path.SetHopField(p.hopField, int( /*@ unfolding acc(p.path.Mem(ubPath), R50) in (unfolding acc(p.path.Base.Mem(), R55) in @*/ p.path.PathMeta.CurrHF /*@ ) @*/) /*@ , ubPath @*/); err != nil {
		// @ sl.CombineRange_Bytes(ub, startP, endP, writePerm)
		// @ fold p.d.validResult(processResult{}, false)
		return processResult{}, serrors.WrapStr("update hop field", err)
	}
	// @ sl.CombineRange_Bytes(ub, startP, endP, writePerm)
	/*@
	ghost var ubLL []byte
	ghost if &p.scionLayer === p.lastLayer {
		ubLL = ub
	} else if llIsNil {
		ubLL = nil
		sl.NilAcc_Bytes()
	} else {
		ubLL = ub[startLL:endLL]
		sl.SplitRange_Bytes(ub, startLL, endLL, writePerm)
		ghost defer sl.CombineRange_Bytes(ub, startLL, endLL, writePerm)
	}
	@*/
	return p.handleSCMPTraceRouteRequest(p.ingressID /*@ , ubLL @*/)
}

// @ preserves acc(&p.infoField, R20)
// @ ensures   res == &p.hopField.EgressRouterAlert || res == &p.hopField.IngressRouterAlert
// @ decreases
func (p *scionPacketProcessor) ingressRouterAlertFlag() (res *bool) {
	if !p.infoField.ConsDir {
		return &p.hopField.EgressRouterAlert
	}
	return &p.hopField.IngressRouterAlert
}

// @ requires  0 <= startLL && startLL <= endLL && endLL <= len(ub)
// @ requires  acc(&p.path, R20)
// @ requires  acc(p.scionLayer.Mem(ub), R14)
// @ requires  p.path === p.scionLayer.GetPath(ub)
// @ requires  acc(&p.d, R20) && acc(p.d.Mem(), _)
// @ preserves sl.AbsSlice_Bytes(ub, 0, len(ub))
// @ preserves acc(&p.lastLayer, R19)
// @ preserves p.lastLayer != nil
// @ preserves (&p.scionLayer !== p.lastLayer && llIsNil) ==>
// @ 	acc(p.lastLayer.Mem(nil), R15)
// @ preserves (&p.scionLayer !== p.lastLayer && !llIsNil) ==>
// @ 	acc(p.lastLayer.Mem(ub[startLL:endLL]), R15)
// @ preserves acc(&p.ingressID, R20)
// @ preserves acc(&p.infoField, R20)
// @ preserves acc(&p.hopField)
// @ ensures   acc(&p.path, R20)
// @ ensures   acc(p.scionLayer.Mem(ub), R14)
// @ ensures   acc(&p.d, R20)
// @ ensures   p.d.validResult(respr, false)
// @ ensures   respr.OutPkt != nil ==>
// @ 	reserr != nil && sl.AbsSlice_Bytes(respr.OutPkt, 0, len(respr.OutPkt))
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// @ decreases
func (p *scionPacketProcessor) handleEgressRouterAlert( /*@ ghost ub []byte, ghost llIsNil bool, ghost startLL int, ghost endLL int @*/ ) (respr processResult, reserr error) {
	// @ ghost ubPath := p.scionLayer.UBPath(ub)
	// @ ghost startP := p.scionLayer.PathStartIdx(ub)
	// @ ghost endP   := p.scionLayer.PathEndIdx(ub)
	// @ assert ub[startP:endP] === ubPath

	alert := p.egressRouterAlertFlag()
	if !*alert {
		// @ fold p.d.validResult(processResult{}, false)
		return processResult{}, nil
	}
	egressID := p.egressInterface()
	// @ p.d.getExternalMem()
	// @ if p.d.external != nil { unfold acc(accBatchConn(p.d.external), _) }
	if _, ok := p.d.external[egressID]; !ok {
		// @ fold p.d.validResult(processResult{}, false)
		return processResult{}, nil
	}
	*alert = false
	// @ unfold acc(p.scionLayer.Mem(ub), R20)
	// @ defer fold acc(p.scionLayer.Mem(ub), R20)
	// (VerifiedSCION) the following is guaranteed by the type system,
	// but Gobra cannot prove it yet
	// @ assume 0 <= p.path.GetCurrHF(ubPath)
	// @ sl.SplitRange_Bytes(ub, startP, endP, writePerm)
	if err := p.path.SetHopField(p.hopField, int( /*@ unfolding acc(p.path.Mem(ubPath), R50) in (unfolding acc(p.path.Base.Mem(), R55) in @*/ p.path.PathMeta.CurrHF /*@ ) @*/) /*@ , ubPath @*/); err != nil {
		// @ sl.CombineRange_Bytes(ub, startP, endP, writePerm)
		// @ fold p.d.validResult(processResult{}, false)
		return processResult{}, serrors.WrapStr("update hop field", err)
	}
	// @ sl.CombineRange_Bytes(ub, startP, endP, writePerm)
	/*@
	ghost var ubLL []byte
	ghost if &p.scionLayer === p.lastLayer {
		ubLL = ub
	} else if llIsNil {
		ubLL = nil
		sl.NilAcc_Bytes()
	} else {
		ubLL = ub[startLL:endLL]
		sl.SplitRange_Bytes(ub, startLL, endLL, writePerm)
		ghost defer sl.CombineRange_Bytes(ub, startLL, endLL, writePerm)
	}
	@*/
	return p.handleSCMPTraceRouteRequest(egressID /*@ , ubLL @*/)
}

// @ preserves acc(&p.infoField, R20)
// @ ensures   res == &p.hopField.IngressRouterAlert || res == &p.hopField.EgressRouterAlert
// @ decreases
func (p *scionPacketProcessor) egressRouterAlertFlag() (res *bool) {
	if !p.infoField.ConsDir {
		return &p.hopField.IngressRouterAlert
	}
	return &p.hopField.EgressRouterAlert
}

// @ requires  acc(&p.lastLayer, R20)
// @ requires  p.lastLayer != nil && acc(p.lastLayer.Mem(ubLastLayer), R15)
// @ requires  acc(&p.d, R20) && acc(p.d.Mem(), _)
// @ preserves sl.AbsSlice_Bytes(ubLastLayer, 0, len(ubLastLayer))
// @ ensures   acc(&p.lastLayer, R20)
// @ ensures   acc(p.lastLayer.Mem(ubLastLayer), R15)
// @ ensures   acc(&p.d, R20)
// @ ensures   p.d.validResult(respr, false)
// @ ensures   respr.OutPkt != nil ==>
// @ 	reserr != nil && sl.AbsSlice_Bytes(respr.OutPkt, 0, len(respr.OutPkt))
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// @ decreases
func (p *scionPacketProcessor) handleSCMPTraceRouteRequest(
	interfaceID uint16 /*@ , ghost ubLastLayer []byte @*/) (respr processResult, reserr error) {

	if p.lastLayer.NextLayerType( /*@ ubLastLayer @*/ ) != slayers.LayerTypeSCMP {
		log.Debug("Packet with router alert, but not SCMP")
		// @ fold p.d.validResult(processResult{}, false)
		return processResult{}, nil
	}
	scionPld /*@ , start, end @*/ := p.lastLayer.LayerPayload( /*@ ubLastLayer @*/ )
	// @ assert scionPld === ubLastLayer[start:end] || scionPld == nil
	// @ if scionPld == nil { sl.NilAcc_Bytes() } else {
	// @	sl.SplitRange_Bytes(ubLastLayer, start, end, writePerm)
	// @ 	ghost defer sl.CombineRange_Bytes(ubLastLayer, start, end, writePerm)
	// @ }
	// @ gopacket.AssertInvariantNilDecodeFeedback()
	var scmpH /*@@@*/ slayers.SCMP
	// @ fold scmpH.NonInitMem()
	if err := scmpH.DecodeFromBytes(scionPld, gopacket.NilDecodeFeedback); err != nil {
		log.Debug("Parsing SCMP header of router alert", "err", err)
		// @ fold p.d.validResult(processResult{}, false)
		return processResult{}, nil
	}
	if /*@ (unfolding acc(scmpH.Mem(scionPld), R55) in @*/ scmpH.TypeCode /*@ ) @*/ != slayers.CreateSCMPTypeCode(slayers.SCMPTypeTracerouteRequest, 0) {
		log.Debug("Packet with router alert, but not traceroute request",
			"type_code", ( /*@ unfolding acc(scmpH.Mem(scionPld), R55) in @*/ scmpH.TypeCode))
		// @ fold p.d.validResult(processResult{}, false)
		return processResult{}, nil
	}
	var scmpP /*@@@*/ slayers.SCMPTraceroute
	// @ fold scmpP.NonInitMem()
	// @ unfold scmpH.Mem(scionPld)
	// @ unfold scmpH.BaseLayer.Mem(scionPld, 4)
	// @ sl.SplitRange_Bytes(scionPld, 4, len(scionPld), writePerm)
	// @ ghost defer sl.CombineRange_Bytes(scionPld, 4, len(scionPld), writePerm)
	if err := scmpP.DecodeFromBytes(scmpH.Payload, gopacket.NilDecodeFeedback); err != nil {
		log.Debug("Parsing SCMPTraceroute", "err", err)
		// @ fold p.d.validResult(processResult{}, false)
		return processResult{}, nil
	}
	// @ unfold scmpP.Mem(scmpH.Payload)
	// @ unfold scmpP.BaseLayer.Mem(scmpH.Payload, 4+addr.IABytes+slayers.scmpRawInterfaceLen)
	// @ p.d.getLocalIA()
	scmpP = slayers.SCMPTraceroute{
		Identifier: scmpP.Identifier,
		Sequence:   scmpP.Sequence,
		IA:         p.d.localIA,
		Interface:  uint64(interfaceID),
	}
	// @ TODO()
	return p.packSCMP(slayers.SCMPTypeTracerouteReply, 0, &scmpP, nil)
}

// @ preserves acc(p.scionLayer.Mem(ubScionL), R20)
// @ preserves acc(&p.d, R50) && acc(p.d.Mem(), _)
// @ ensures   p.d.validResult(respr, false)
// @ ensures   respr.OutPkt != nil ==> reserr != nil && sl.AbsSlice_Bytes(respr.OutPkt, 0, len(respr.OutPkt))
// @ ensures   reserr == nil ==> int(p.scionLayer.GetPayloadLen(ubScionL)) == len(p.scionLayer.GetPayload(ubScionL))
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// @ decreases
func (p *scionPacketProcessor) validatePktLen( /*@ ghost ubScionL []byte @*/ ) (respr processResult, reserr error) {
	// @ unfold acc(p.scionLayer.Mem(ubScionL), R20)
	// @ defer fold acc(p.scionLayer.Mem(ubScionL), R20)
	if int(p.scionLayer.PayloadLen) == len(p.scionLayer.Payload) {
		// @ fold p.d.validResult(processResult{}, false)
		return processResult{}, nil
	}
	// @ TODO()
	return p.packSCMP(
		slayers.SCMPTypeParameterProblem,
		slayers.SCMPCodeInvalidPacketSize,
		&slayers.SCMPParameterProblem{Pointer: 0},
		serrors.New("bad packet size",
			"header", p.scionLayer.PayloadLen, "actual", len(p.scionLayer.Payload)),
	)
}

// @ requires  0 <= startLL && startLL <= endLL && endLL <= len(ub)
// @ requires  acc(&p.d, R5) && acc(p.d.Mem(), _) && p.d.WellConfigured()
// @ requires  p.d.getValSvc() != nil
// The ghost param ub here allows us to introduce a bound variable to p.rawPkt,
// which slightly simplifies the spec
// @ requires  acc(&p.rawPkt, R1) && ub === p.rawPkt
// @ requires  acc(&p.path, R10)
// @ requires  p.scionLayer.Mem(ub)
// @ requires  p.path == p.scionLayer.GetPath(ub)
// @ requires  sl.AbsSlice_Bytes(ub, 0, len(ub))
// @ preserves acc(&p.srcAddr, R10) && acc(p.srcAddr.Mem(), _)
// @ preserves acc(&p.lastLayer, R10)
// @ preserves p.lastLayer != nil
// @ preserves (p.lastLayer !== &p.scionLayer && llIsNil) ==>
// @ 	acc(p.lastLayer.Mem(nil), R10)
// @ preserves (p.lastLayer !== &p.scionLayer && !llIsNil) ==>
// @ 	acc(p.lastLayer.Mem(ub[startLL:endLL]), R10)
// @ preserves acc(&p.ingressID, R20)
// @ preserves acc(&p.infoField)
// @ preserves acc(&p.hopField)
// @ preserves acc(&p.segmentChange)
// @ preserves acc(&p.mac, R10) && p.mac != nil && p.mac.Mem()
// @ preserves acc(&p.macBuffers.scionInput, R10)
// @ preserves sl.AbsSlice_Bytes(p.macBuffers.scionInput, 0, len(p.macBuffers.scionInput))
// @ preserves acc(&p.cachedMac)
// @ ensures   acc(&p.d, R5)
// @ ensures   acc(&p.path, R10)
// @ ensures   acc(&p.rawPkt, R1)
// @ ensures   acc(sl.AbsSlice_Bytes(ub, 0, len(ub)), 1 - R15)
// @ ensures   p.d.validResult(respr, addrAliasesPkt)
// @ ensures   addrAliasesPkt ==> (
// @ 	respr.OutAddr != nil &&
// @ 	(acc(respr.OutAddr.Mem(), R15) --* acc(sl.AbsSlice_Bytes(ub, 0, len(ub)), R15)))
// @ ensures   !addrAliasesPkt ==> acc(sl.AbsSlice_Bytes(ub, 0, len(ub)), R15)
// @ ensures   respr.OutPkt !== ub && respr.OutPkt != nil ==>
// @ 	sl.AbsSlice_Bytes(respr.OutPkt, 0, len(respr.OutPkt))
// @ ensures   reserr == nil ==> p.scionLayer.Mem(ub)
// @ ensures   reserr != nil ==> p.scionLayer.NonInitMem()
// @ ensures   reserr != nil ==> reserr.ErrorMem()
func (p *scionPacketProcessor) process( /*@ ghost ub []byte, ghost llIsNil bool, ghost startLL int, ghost endLL int @*/ ) (respr processResult, reserr error /*@, addrAliasesPkt bool @*/) {
	if r, err := p.parsePath( /*@ ub @*/ ); err != nil {
		// @ p.scionLayer.DowngradePerm(ub)
		return r, err /*@, false @*/
	}
	if r, err := p.validateHopExpiry(); err != nil {
		// @ p.scionLayer.DowngradePerm(ub)
		return r, err /*@, false @*/
	}
	if r, err := p.validateIngressID(); err != nil {
		// @ p.scionLayer.DowngradePerm(ub)
		return r, err /*@, false @*/
	}
	if r, err := p.validatePktLen( /*@ ub @*/ ); err != nil {
		// @ p.scionLayer.DowngradePerm(ub)
		return r, err /*@, false @*/
	}
	if r, err := p.validateTransitUnderlaySrc( /*@ ub @*/ ); err != nil {
		// @ p.scionLayer.DowngradePerm(ub)
		return r, err /*@, false @*/
	}
	if r, err := p.validateSrcDstIA( /*@ ub @*/ ); err != nil {
		// @ p.scionLayer.DowngradePerm(ub)
		return r, err /*@, false @*/
	}
	if err := p.updateNonConsDirIngressSegID( /*@ ub @*/ ); err != nil {
		// @ p.scionLayer.DowngradePerm(ub)
		return processResult{}, err /*@, false @*/
	}
	if r, err := p.verifyCurrentMAC(); err != nil {
		// @ p.scionLayer.DowngradePerm(ub)
		return r, err /*@, false @*/
	}
	if r, err := p.handleIngressRouterAlert( /*@ ub, llIsNil, startLL, endLL @*/ ); err != nil {
		// @ p.scionLayer.DowngradePerm(ub)
		return r, err /*@, false @*/
	}

	// Inbound: pkts destined to the local IA.
	// @ p.d.getLocalIA()
	if /*@ unfolding acc(p.scionLayer.Mem(ub), R50) in (unfolding acc(p.scionLayer.HeaderMem(ub[slayers.CmnHdrLen:]), R55) in @*/ p.scionLayer.DstIA /*@ ) @*/ == p.d.localIA {
		a, r, err /*@, aliasesUb @*/ := p.resolveInbound( /*@ ub @*/ )
		if err != nil {
			// @ p.scionLayer.DowngradePerm(ub)
			return r, err /*@, aliasesUb @*/
		}
		// @ p.d.getInternal()
		// @ unfold p.d.validResult(r, aliasesUb)
		// @ fold p.d.validResult(processResult{OutConn: p.d.internal, OutAddr: a, OutPkt: p.rawPkt}, aliasesUb)
		// @ assert ub === p.rawPkt
		return processResult{OutConn: p.d.internal, OutAddr: a, OutPkt: p.rawPkt}, nil /*@, aliasesUb @*/
	}

	// Outbound: pkts leaving the local IA.
	// BRTransit: pkts leaving from the same BR different interface.

	// @ unfold acc(p.scionLayer.Mem(ub), R3)
	// @ ghost ubPath := p.scionLayer.UBPath(ub)
	if p.path.IsXover( /*@ ubPath @*/ ) {
		// @ fold acc(p.scionLayer.Mem(ub), R3)
		if r, err := p.doXover( /*@ ub @*/ ); err != nil {
			// @ fold p.d.validResult(r, false)
			return r, err /*@, false @*/
		}
		if r, err := p.validateHopExpiry(); err != nil {
			// @ p.scionLayer.DowngradePerm(ub)
			return r, serrors.WithCtx(err, "info", "after xover") /*@, false @*/
		}
		// verify the new block
		if r, err := p.verifyCurrentMAC(); err != nil {
			//  fold acc(p.scionLayer.Mem(ub), R3)
			// @ p.scionLayer.DowngradePerm(ub)
			return r, serrors.WithCtx(err, "info", "after xover") /*@, false @*/
		}
	}
	// @ fold acc(p.scionLayer.Mem(ub), R3)
	if r, err := p.validateEgressID(); err != nil {
		// @ p.scionLayer.DowngradePerm(ub)
		return r, err /*@, false @*/
	}
	// handle egress router alert before we check if it's up because we want to
	// send the reply anyway, so that trace route can pinpoint the exact link
	// that failed.
	if r, err := p.handleEgressRouterAlert( /*@ ub, llIsNil, startLL, endLL @*/ ); err != nil {
		// @ p.scionLayer.DowngradePerm(ub)
		return r, err /*@, false @*/
	}
	if r, err := p.validateEgressUp(); err != nil {
		// @ p.scionLayer.DowngradePerm(ub)
		return r, err /*@, false @*/
	}
	egressID := p.egressInterface()
	// @ p.d.getExternalMem()
	// @ if p.d.external != nil { unfold acc(accBatchConn(p.d.external), _) }
	if c, ok := p.d.external[egressID]; ok {
		if err := p.processEgress( /*@ ub @*/ ); err != nil {
			// @ fold p.d.validResult(processResult{}, false)
			return processResult{}, err /*@, false @*/
		}
		// @ p.d.InDomainExternalInForwardingMetrics2(egressID)
		// @ fold p.d.validResult(processResult{EgressID: egressID, OutConn: c, OutPkt: p.rawPkt}, false)
		return processResult{EgressID: egressID, OutConn: c, OutPkt: p.rawPkt}, nil /*@, false @*/
	}

	// ASTransit: pkts leaving from another AS BR.
	// @ p.d.getInternalNextHops()
	// @ ghost if p.d.internalNextHops != nil { unfold acc(accAddr(p.d.internalNextHops), _) }
	if a, ok := p.d.internalNextHops[egressID]; ok {
		// @ p.d.getInternal()
		// @ fold p.d.validResult(processResult{OutConn: p.d.internal, OutAddr: a, OutPkt: p.rawPkt}, false)
		return processResult{OutConn: p.d.internal, OutAddr: a, OutPkt: p.rawPkt}, nil /*@, false @*/
	}
	errCode := slayers.SCMPCodeUnknownHopFieldEgress
	if !p.infoField.ConsDir {
		errCode = slayers.SCMPCodeUnknownHopFieldIngress
	}
	// @ TODO()
	// @ p.scionLayer.DowngradePerm(ub)
	tmp, err := p.packSCMP(
		slayers.SCMPTypeParameterProblem,
		errCode,
		&slayers.SCMPParameterProblem{Pointer: p.currentHopPointer( /*@ nil @*/ )},
		cannotRoute,
	)
	return tmp, err /*@, false @*/
}

// @ requires  acc(&p.rawPkt, R15)
// @ requires  p.scionLayer.Mem(p.rawPkt)
// @ requires  acc(&p.ingressID,  R15)
// @ requires  acc(&p.d, R15) && acc(p.d.Mem(), _) && p.d.WellConfigured()
// @ requires  p.d.getValSvc() != nil
// @ requires  sl.AbsSlice_Bytes(p.rawPkt, 0, len(p.rawPkt))
// @ preserves acc(&p.mac, R10)
// @ preserves p.mac != nil && p.mac.Mem()
// @ preserves acc(&p.macBuffers.scionInput, R10)
// @ preserves sl.AbsSlice_Bytes(p.macBuffers.scionInput, 0, len(p.macBuffers.scionInput))
// @ preserves acc(&p.buffer, R10) && p.buffer != nil && p.buffer.Mem()
// @ ensures   acc(&p.rawPkt, R15)
// @ ensures   p.scionLayer.Mem(p.rawPkt)
// @ ensures   acc(&p.ingressID,  R15)
// @ ensures   acc(&p.d,          R15)
// @ ensures   p.d.validResult(respr, addrAliasesPkt)
// @ ensures   acc(sl.AbsSlice_Bytes(p.rawPkt, 0, len(p.rawPkt)), 1 - R15)
// @ ensures   addrAliasesPkt ==> (
// @ 	respr.OutAddr != nil &&
// @ 	let rawPkt := p.rawPkt in
// @ 	(acc(respr.OutAddr.Mem(), R15) --* acc(sl.AbsSlice_Bytes(rawPkt, 0, len(rawPkt)), R15)))
// @ ensures  !addrAliasesPkt ==> acc(sl.AbsSlice_Bytes(p.rawPkt, 0, len(p.rawPkt)), R15)
// @ ensures  respr.OutPkt !== p.rawPkt && respr.OutPkt != nil ==>
// @ 	sl.AbsSlice_Bytes(respr.OutPkt, 0, len(respr.OutPkt))
// @ ensures  reserr != nil ==> reserr.ErrorMem()
func (p *scionPacketProcessor) processOHP() (respr processResult, reserr error /*@ , addrAliasesPkt bool @*/) {
	// @ ghost ubScionL := p.rawPkt
	// @ p.scionLayer.ExtractAcc(ubScionL)
	s := p.scionLayer
	// @ ghost  ubPath := p.scionLayer.UBPath(ubScionL)
	// @ unfold acc(p.scionLayer.Mem(ubScionL), 1-R15)
	// @ apply acc(&p.scionLayer, R16) --* acc(p.scionLayer.Mem(ubScionL), R15)
	// @ unfold acc(p.scionLayer.Mem(ubScionL), R15)
	// @ assert s.Path === p.scionLayer.Path
	// @ assert s.Path.Mem(ubPath)
	ohp, ok := s.Path.(*onehop.Path)
	if !ok {
		// TODO parameter problem -> invalid path
		// @ establishMemMalformedPath()
		// @ fold p.scionLayer.Mem(ubScionL)
		// @ fold p.d.validResult(processResult{}, false)
		return processResult{}, malformedPath /*@ , false @*/
	}
	if /*@ unfolding acc(s.Path.Mem(ubPath), R50) in @*/ !ohp.Info.ConsDir {
		// TODO parameter problem -> invalid path
		// @ establishMemMalformedPath()
		// @ defer fold p.scionLayer.Mem(ubScionL)
		// @ fold p.d.validResult(processResult{}, false)
		return processResult{}, serrors.WrapStr(
			"OneHop path in reverse construction direction is not allowed",
			malformedPath, "srcIA", s.SrcIA, "dstIA", s.DstIA) /*@ , false @*/
	}

	// OHP leaving our IA
	if p.ingressID == 0 {
		// @ p.d.getLocalIA()
		if !p.d.localIA.Equal(s.SrcIA) {
			// @ establishCannotRoute()
			// TODO parameter problem -> invalid path
			// @ defer fold p.scionLayer.Mem(ubScionL)
			// @ fold p.d.validResult(processResult{}, false)
			return processResult{}, serrors.WrapStr("bad source IA", cannotRoute,
				"type", "ohp", "egress", ( /*@ unfolding acc(ohp.Mem(ubPath), R50) in (unfolding acc(ohp.FirstHop.Mem(), R55) in @*/ ohp.FirstHop.ConsEgress /*@ ) @*/),
				"localIA", p.d.localIA, "srcIA", s.SrcIA) /*@ , false @*/
		}
		// @ p.d.getNeighborIAs()
		neighborIA, ok := p.d.neighborIAs[ /*@ unfolding acc(ohp.Mem(ubPath), R50) in (unfolding acc(ohp.FirstHop.Mem(), R55) in @*/ ohp.FirstHop.ConsEgress /*@ ) @*/]
		if !ok {
			// @ establishCannotRoute()
			// TODO parameter problem invalid interface
			// @ defer fold p.scionLayer.Mem(ubScionL)
			// @ fold p.d.validResult(processResult{}, false)
			return processResult{}, serrors.WithCtx(cannotRoute,
				"type", "ohp", "egress", ( /*@ unfolding acc(ohp.Mem(ubPath), R50) in (unfolding acc(ohp.FirstHop.Mem(), R55) in @*/ ohp.FirstHop.ConsEgress /*@ ) @*/)) /*@ , false @*/
		}
		if !neighborIA.Equal(s.DstIA) {
			// @ establishCannotRoute()
			// @ defer fold p.scionLayer.Mem(ubScionL)
			// @ fold p.d.validResult(processResult{}, false)
			return processResult{}, serrors.WrapStr("bad destination IA", cannotRoute,
				"type", "ohp", "egress", ( /*@ unfolding acc(ohp.Mem(ubPath), R50) in (unfolding acc(ohp.FirstHop.Mem(), R55) in @*/ ohp.FirstHop.ConsEgress /*@ ) @*/),
				"neighborIA", neighborIA, "dstIA", s.DstIA) /*@ , false @*/
		}
		// @ unfold s.Path.Mem(ubPath)
		// @ unfold ohp.FirstHop.Mem()
		// @ preserves acc(&ohp.Info, R15) && acc(&ohp.FirstHop, R15)
		// @ preserves acc(&p.macBuffers.scionInput, R15)
		// @ preserves acc(&p.mac, R15) && p.mac != nil && p.mac.Mem()
		// @ preserves sl.AbsSlice_Bytes(p.macBuffers.scionInput, 0, len(p.macBuffers.scionInput))
		// @ decreases
		// @ outline (
		mac /*@@@*/ := path.MAC(p.mac, ohp.Info, ohp.FirstHop, p.macBuffers.scionInput)
		// (VerifiedSCION) introduced separate copy to avoid exposing quantified permissions outside the scope of this outline block.
		macCopy := mac
		// @ fold acc(sl.AbsSlice_Bytes(ohp.FirstHop.Mac[:], 0, len(ohp.FirstHop.Mac[:])), R20)
		// @ fold acc(sl.AbsSlice_Bytes(mac[:], 0, len(mac)), R20)
		compRes := subtle.ConstantTimeCompare(ohp.FirstHop.Mac[:], mac[:]) == 0
		// @ unfold acc(sl.AbsSlice_Bytes(ohp.FirstHop.Mac[:], 0, len(ohp.FirstHop.Mac[:])), R20)
		// @ )
		if compRes {
			// @ defer fold p.scionLayer.Mem(ubScionL)
			// @ defer fold s.Path.Mem(ubPath)
			// @ defer fold ohp.FirstHop.Mem()
			// TODO parameter problem -> invalid MAC
			// @ fold p.d.validResult(processResult{}, false)
			return processResult{}, serrors.New("MAC", "expected", fmt.Sprintf("%x", macCopy),
				"actual", fmt.Sprintf("%x", ohp.FirstHop.Mac), "type", "ohp") /*@ , false @*/
		}
		ohp.Info.UpdateSegID(ohp.FirstHop.Mac)
		// @ fold ohp.FirstHop.Mem()
		// @ fold s.Path.Mem(ubPath)
		// @ fold p.scionLayer.Mem(ubScionL)

		// (VerifiedSCION) the second parameter was changed from 's' to 'p.scionLayer' due to the
		// changes made to 'updateSCIONLayer'.
		if err := updateSCIONLayer(p.rawPkt, &p.scionLayer /* s */, p.buffer); err != nil {
			// @ fold p.d.validResult(processResult{}, false)
			return processResult{}, err /*@ , false @*/
		}
		// @ unfold p.scionLayer.Mem(ubScionL)
		// @ defer fold p.scionLayer.Mem(ubScionL)
		// @ unfold s.Path.Mem(ubPath)
		// @ defer fold s.Path.Mem(ubPath)
		// @ unfold ohp.FirstHop.Mem()
		// @ defer fold ohp.FirstHop.Mem()
		// OHP should always be directed to the correct BR.
		// @ p.d.getExternalMem()
		// @ ghost if p.d.external != nil { unfold acc(accBatchConn(p.d.external), _) }
		if c, ok := p.d.external[ohp.FirstHop.ConsEgress]; ok {
			// (VerifiedSCION) the following must hold, obviously.
			// Unfortunately, Gobra struggles with instantiating the body
			// of the function.
			// @ assume ohp.FirstHop.ConsEgress in p.d.getDomExternal()
			// buffer should already be correct
			// (VerifiedSCION) TODO: we need to add a pre to run that says that the
			// domain of forwardingMetrics is the same as the one for external
			// @ p.d.InDomainExternalInForwardingMetrics(ohp.FirstHop.ConsEgress)
			// @ fold p.d.validResult(processResult{EgressID: ohp.FirstHop.ConsEgress, OutConn: c, OutPkt: p.rawPkt}, false)
			return processResult{EgressID: ohp.FirstHop.ConsEgress, OutConn: c, OutPkt: p.rawPkt},
				nil /*@ , false @*/
		}
		// TODO parameter problem invalid interface
		// @ establishCannotRoute()
		// @ fold p.d.validResult(processResult{}, false)
		return processResult{}, serrors.WithCtx(cannotRoute, "type", "ohp",
			"egress", ohp.FirstHop.ConsEgress, "consDir", ohp.Info.ConsDir) /*@ , false @*/
	}

	// OHP entering our IA
	// @ p.d.getLocalIA()
	if !p.d.localIA.Equal(s.DstIA) {
		// @ establishCannotRoute()
		// @ defer fold p.scionLayer.Mem(ubScionL)
		// @ fold p.d.validResult(processResult{}, false)
		return processResult{}, serrors.WrapStr("bad destination IA", cannotRoute,
			"type", "ohp", "ingress", p.ingressID,
			"localIA", p.d.localIA, "dstIA", s.DstIA) /*@ , false @*/
	}
	// @ p.d.getNeighborIAs()
	neighborIA := p.d.neighborIAs[p.ingressID]
	if !neighborIA.Equal(s.SrcIA) {
		// @ establishCannotRoute()
		// @ defer fold p.scionLayer.Mem(ubScionL)
		// @ fold p.d.validResult(processResult{}, false)
		return processResult{}, serrors.WrapStr("bad source IA", cannotRoute,
			"type", "ohp", "ingress", p.ingressID,
			"neighborIA", neighborIA, "srcIA", s.SrcIA) /*@ , false @*/
	}

	// @ unfold s.Path.Mem(ubPath)
	// @ unfold ohp.SecondHop.Mem()
	ohp.SecondHop = path.HopField{
		ConsIngress: p.ingressID,
		ExpTime:/*@ unfolding acc(ohp.FirstHop.Mem(), R55) in @*/ ohp.FirstHop.ExpTime,
	}
	// (VerifiedSCION) the following property follows from the type system, but
	// Gobra cannot prove it yet.
	// @ assume 0 <= p.ingressID
	// XXX(roosd): Here we leak the buffer into the SCION packet header.
	// This is okay because we do not operate on the buffer or the packet
	// for the rest of processing.
	ohp.SecondHop.Mac = path.MAC(p.mac, ohp.Info, ohp.SecondHop, p.macBuffers.scionInput)
	// @ fold ohp.SecondHop.Mem()
	// @ fold s.Path.Mem(ubPath)

	// (VerifiedSCION) the second parameter was changed from 's' to 'p.scionLayer' due to the
	// changes made to 'updateSCIONLayer'.
	// @ fold p.scionLayer.Mem(ubScionL)
	if err := updateSCIONLayer(p.rawPkt, &p.scionLayer /* s */, p.buffer); err != nil {
		// @ fold p.d.validResult(processResult{}, false)
		return processResult{}, err /*@ , false @*/
	}
	// (VerifiedSCION) the parameter was changed from 's' to '&p.scionLayer' due to the
	// changes made to 'resolveLocalDst'.
	a, err /*@ , addrAliases @*/ := p.d.resolveLocalDst(&p.scionLayer /* s */ /*@ , ubScionL @*/)
	if err != nil {
		// @ ghost if addrAliases {
		// @ 	apply acc(a.Mem(), R15) --* acc(sl.AbsSlice_Bytes(ubScionL, 0, len(ubScionL)), R15)
		// @ }
		// @ fold p.d.validResult(processResult{}, false)
		return processResult{}, err /*@ , false @*/
	}
	// @ p.d.getInternal()
	// @ assert p.d.internal != nil ==> acc(p.d.internal.Mem(), _)
	// @ fold p.d.validResult(processResult{OutConn: p.d.internal, OutAddr: a, OutPkt: p.rawPkt}, addrAliases)
	return processResult{OutConn: p.d.internal, OutAddr: a, OutPkt: p.rawPkt}, nil /*@ , addrAliases @*/
}

// @ requires  acc(d.Mem(), _)
// @ requires  d.getValSvc() != nil
// @ requires  acc(sl.AbsSlice_Bytes(ub, 0, len(ub)), R15)
// @ preserves acc(s.Mem(ub), R14)
// @ ensures   !addrAliasesUb ==> acc(sl.AbsSlice_Bytes(ub, 0, len(ub)), R15)
// @ ensures   !addrAliasesUb && resaddr != nil ==> acc(resaddr.Mem(), _)
// @ ensures   addrAliasesUb ==> resaddr != nil
// @ ensures   addrAliasesUb ==> acc(resaddr.Mem(), R15)
// @ ensures   addrAliasesUb ==> (acc(resaddr.Mem(), R15) --* acc(sl.AbsSlice_Bytes(ub, 0, len(ub)), R15))
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// (VerifiedSCION) the type of 's' was changed from slayers.SCION to *slayers.SCION. This makes
// specs a lot easier and, makes the implementation faster as well by avoiding passing large data-structures
// by value. We should consider porting merging this in upstream SCION.
func (d *DataPlane) resolveLocalDst(s *slayers.SCION /*@, ghost ub []byte @*/) (resaddr *net.UDPAddr, reserr error /*@ , addrAliasesUb bool @*/) {
	// @ ghost start, end := s.ExtractAcc(ub)
	// @ assert s.RawDstAddr === ub[start:end]
	// @ sl.SplitRange_Bytes(ub, start, end, R15)
	// @ assert acc(sl.AbsSlice_Bytes(s.RawDstAddr, 0, len(s.RawDstAddr)), R15)
	dst, err := s.DstAddr()
	// @ apply acc(s, R16) --* acc(s.Mem(ub), R15)
	if err != nil {
		// @ sl.CombineRange_Bytes(ub, start, end, R15)
		// TODO parameter problem.
		return nil, err /*@ , false @*/
	}
	switch v := dst.(type) {
	case addr.HostSVC:
		// For map lookup use the Base address, i.e. strip the multi cast
		// information, because we only register base addresses in the map.
		// @ d.getSvcMem()
		a, ok := d.svc.Any(v.Base())
		if !ok {
			// @ apply acc(dst.Mem(), R15) --* acc(sl.AbsSlice_Bytes(ub[start:end], 0, len(ub[start:end])), R15)
			// @ sl.CombineRange_Bytes(ub, start, end, R15)
			// @ establishNoSVCBackend()
			return nil, noSVCBackend /*@ , false @*/
		}
		// @ apply acc(dst.Mem(), R15) --* acc(sl.AbsSlice_Bytes(ub[start:end], 0, len(ub[start:end])), R15)
		// @ sl.CombineRange_Bytes(ub, start, end, R15)
		return a, nil /*@ , false @*/
	case *net.IPAddr:
		tmp := addEndhostPort(v)
		// @ package acc(tmp.Mem(), R15) --* acc(sl.AbsSlice_Bytes(ub, 0, len(ub)), R15) {
		// @ 	apply acc(tmp.Mem(), R15) --* acc(v.Mem(), R15)
		// @ 	assert acc(dst.Mem(), R15)
		// @ 	apply acc(dst.Mem(), R15) --* acc(sl.AbsSlice_Bytes(ub[start:end], 0, len(ub[start:end])), R15)
		// @ 	sl.CombineRange_Bytes(ub, start, end, R15)
		// @ }
		return tmp, nil /*@ , true @*/
	default:
		panic("unexpected address type returned from DstAddr")
	}
}

// @ requires acc(dst.Mem(), R15)
// @ ensures  res != nil && acc(res.Mem(), R15)
// @ ensures  acc(res.Mem(), R15) --* acc(dst.Mem(), R15)
// @ decreases
func addEndhostPort(dst *net.IPAddr) (res *net.UDPAddr) {
	// @ unfold acc(dst.Mem(), R15)
	tmp := &net.UDPAddr{IP: dst.IP, Port: topology.EndhostPort}
	// @ assert forall i int :: { &tmp.IP[i] } 0 <= i && i < len(tmp.IP) ==> acc(&tmp.IP[i], R15)
	// @ fold acc(sl.AbsSlice_Bytes(tmp.IP, 0, len(tmp.IP)), R15)
	// @ fold acc(tmp.Mem(), R15)
	// @ package (acc(tmp.Mem(), R15) --* acc(dst.Mem(), R15)) {
	// @ 	assert acc(dst, R15)
	// @ 	assert acc(tmp, R50)
	// @ 	assert dst.IP === tmp.IP
	// @ 	unfold acc(tmp.Mem(), R15)
	// @ 	unfold acc(sl.AbsSlice_Bytes(tmp.IP, 0, len(tmp.IP)), R15)
	// @ 	assert forall i int :: { &tmp.IP[i] } 0 <= i && i < len(tmp.IP) ==> acc(&tmp.IP[i], R15)
	// @ 	assert forall i int :: { &dst.IP[i] } 0 <= i && i < len(dst.IP) ==> acc(&dst.IP[i], R15)
	// @ 	fold acc(dst.Mem(), R15)
	// @ }
	return tmp
}

// TODO(matzf) this function is now only used to update the OneHop-path.
// This should be changed so that the OneHop-path can be updated in-place, like
// the scion.Raw path.
// @ requires  acc(s.Mem(rawPkt), R00)
// @ requires  s.HasOneHopPath(rawPkt)
// @ preserves buffer != nil && buffer.Mem()
// @ preserves sl.AbsSlice_Bytes(rawPkt, 0, len(rawPkt))
// @ ensures   acc(s.Mem(rawPkt), R00)
// @ ensures   res != nil ==> res.ErrorMem()
// @ decreases
// (VerifiedSCION) the type of 's' was changed from slayers.SCION to *slayers.SCION. This makes
// specs a lot easier and, makes the implementation faster as well by avoiding passing large data-structures
// by value. We should consider porting merging this in upstream SCION.
func updateSCIONLayer(rawPkt []byte, s *slayers.SCION, buffer gopacket.SerializeBuffer) (res error) {
	if err := buffer.Clear(); err != nil {
		return err
	}
	if err := s.SerializeTo(buffer, gopacket.SerializeOptions{} /*@ , rawPkt @*/); err != nil {
		return err
	}
	// TODO(lukedirtwalker): We should add a method to the scion layers
	// which can write into the existing buffer, see also the discussion in
	// https://fsnets.slack.com/archives/C8ADBBG0J/p1592805884250700
	rawContents := buffer.Bytes()
	// @ s.InferSizeOHP(rawPkt)
	// @ assert len(rawContents) <= len(rawPkt)
	// @ unfold sl.AbsSlice_Bytes(rawPkt, 0, len(rawPkt))
	// @ unfold acc(sl.AbsSlice_Bytes(rawContents, 0, len(rawContents)), R20)
	// (VerifiedSCION) proving that the reslicing operation below is safe
	// was tricky and required enriching (non-modularly) the invariants of *onehop.Path
	// and *slayers.SCION.
	// @ assert forall i int :: { &rawPkt[:len(rawContents)][i] }{ &rawPkt[i] } 0 <= i && i < len(rawContents) ==>
	// @ 	 &rawPkt[i] == &rawPkt[:len(rawContents)][i]
	copy(rawPkt[:len(rawContents)], rawContents /*@ , R20 @*/)
	// @ fold sl.AbsSlice_Bytes(rawPkt, 0, len(rawPkt))
	// @ fold acc(sl.AbsSlice_Bytes(rawContents, 0, len(rawContents)), R20)
	// @ buffer.RestoreMem(rawContents)
	return nil
}

type bfdSend struct {
	conn             BatchConn
	srcAddr, dstAddr *net.UDPAddr
	scn              *slayers.SCION
	ohp              *onehop.Path
	mac              hash.Hash
	macBuffer        []byte
	buffer           gopacket.SerializeBuffer
}

// newBFDSend creates and initializes a BFD Sender
// @ trusted
// @ requires false
// @ decreases
func newBFDSend(conn BatchConn, srcIA, dstIA addr.IA, srcAddr, dstAddr *net.UDPAddr,
	ifID uint16, mac hash.Hash) (res *bfdSend) {

	scn := &slayers.SCION{
		Version:      0,
		TrafficClass: 0xb8,
		FlowID:       0xdead,
		NextHdr:      slayers.L4BFD,
		SrcIA:        srcIA,
		DstIA:        dstIA,
	}

	if err := scn.SetSrcAddr(&net.IPAddr{IP: srcAddr.IP} /*@ , false @*/); err != nil {
		panic(err) // Must work unless IPAddr is not supported
	}
	if err := scn.SetDstAddr(&net.IPAddr{IP: dstAddr.IP} /*@ , false @*/); err != nil {
		panic(err) // Must work unless IPAddr is not supported
	}

	var ohp *onehop.Path
	if ifID == 0 {
		scn.PathType = empty.PathType
		scn.Path = &empty.Path{}
	} else {
		ohp = &onehop.Path{
			Info: path.InfoField{
				ConsDir: true,
				// Timestamp set in Send
			},
			FirstHop: path.HopField{
				ConsEgress: ifID,
				ExpTime:    hopFieldDefaultExpTime,
			},
		}
		scn.PathType = onehop.PathType
		scn.Path = ohp
	}

	return &bfdSend{
		conn:      conn,
		srcAddr:   srcAddr,
		dstAddr:   dstAddr,
		scn:       scn,
		ohp:       ohp,
		mac:       mac,
		macBuffer: make([]byte, path.MACBufferSize),
		buffer:    gopacket.NewSerializeBuffer(),
	}
}

// @ preserves acc(b.Mem(), R10)
// @ decreases
func (b *bfdSend) String() string {
	// @ unfold acc(b.Mem(), R10)
	// @ ghost defer fold acc(b.Mem(), R10)
	return b.srcAddr.String()
}

// Send sends out a BFD message.
// Due to the internal state of the MAC computation, this is not goroutine
// safe.
// @ trusted
// @ requires Uncallable()
func (b *bfdSend) Send(bfd *layers.BFD) error {
	if b.ohp != nil {
		// Subtract 10 seconds to deal with possible clock drift.
		ohp := b.ohp
		ohp.Info.Timestamp = uint32(time.Now().Unix() - 10)
		ohp.FirstHop.Mac = path.MAC(b.mac, ohp.Info, ohp.FirstHop, b.macBuffer)
	}

	err := gopacket.SerializeLayers(b.buffer, gopacket.SerializeOptions{FixLengths: true},
		b.scn, bfd)
	if err != nil {
		return err
	}
	_, err = b.conn.WriteTo(b.buffer.Bytes(), b.dstAddr)
	return err
}

// @ requires  acc(&p.d, _) && acc(p.d.Mem(), _)
// @ requires  acc(p.scionLayer.Mem(ub), R4)
// @ requires  p.scionLayer.ValidPathMetaData(ub)
// @ requires  sl.AbsSlice_Bytes(ub, 0, len(ub))
// @ requires  acc(&p.ingressID,  R15)
// @ ensures   acc(p.scionLayer.Mem(ub), R4)
// @ ensures   sl.AbsSlice_Bytes(ub, 0, len(ub))
// @ ensures   acc(&p.ingressID,  R15)
// @ decreases
func (p *scionPacketProcessor) prepareSCMP(
	typ slayers.SCMPType,
	code slayers.SCMPCode,
	scmpP gopacket.SerializableLayer,
	cause error,
	// @ ghost ub []byte,
) ([]byte, error) {

	// *copy* and reverse path -- the original path should not be modified as this writes directly
	// back to rawPkt (quote).
	var path *scion.Raw
	// @ ghost startP := p.scionLayer.PathStartIdx(ub)
	// @ ghost endP := p.scionLayer.PathEndIdx(ub)
	// @ slayers.LemmaPathIdxStartEnd(&p.scionLayer, ub, R20)
	// @ ghost ubPath := ub[startP:endP]
	// @ unfold acc(p.scionLayer.Mem(ub), R4)
	pathType := p.scionLayer.Path.Type( /*@ ubPath @*/ )
	// @ establishCannotRoute()
	// @ ghost pathFromEpic := false
	// @ ghost var epicPathUb []byte = nil
	switch pathType {
	case scion.PathType:
		var ok bool
		path, ok = p.scionLayer.Path.(*scion.Raw)
		if !ok {
			// @ fold acc(p.scionLayer.Mem(ub), R4)
			return nil, serrors.WithCtx(cannotRoute, "details", "unsupported path type",
				"path type", pathType)
		}
	case epic.PathType:
		epicPath, ok := p.scionLayer.Path.(*epic.Path)
		if !ok {
			// @ fold acc(p.scionLayer.Mem(ub), R4)
			return nil, serrors.WithCtx(cannotRoute, "details", "unsupported path type",
				"path type", pathType)
		}
		/*@
		scionBuf := epicPath.GetUnderlyingScionPathBuf(ubPath)
		unfold acc(epicPath.Mem(ubPath), R4)
		assert ubPath[epic.MetadataLen:] === scionBuf
		epicPathUb = ubPath
		ubPath = scionBuf
		startP += epic.MetadataLen
		assert ubPath === ub[startP:endP]
		@*/
		path = epicPath.ScionPath
		// @ pathFromEpic = true
	default:
		// @ fold acc(p.scionLayer.Mem(ub), R4)
		return nil, serrors.WithCtx(cannotRoute, "details", "unsupported path type",
			"path type", pathType)
	}
	/*@
	assert pathType == scion.PathType || pathType == epic.PathType
	assert typeOf(p.scionLayer.Path) == type[*scion.Raw] || typeOf(p.scionLayer.Path) == type[*epic.Path]
	assert !pathFromEpic ==> typeOf(p.scionLayer.Path) == type[*scion.Raw]
	assert pathFromEpic ==> typeOf(p.scionLayer.Path) == type[*epic.Path]
	sl.SplitRange_Bytes(ub, startP, endP, writePerm)
	@*/
	decPath, err := path.ToDecoded( /*@ ubPath @*/ )
	if err != nil {
		/*@
		sl.CombineRange_Bytes(ub, startP, endP, writePerm)
		ghost if pathFromEpic {
			epicPath := p.scionLayer.Path.(*epic.Path)
			assert acc(path.Mem(ubPath), R4)
			fold acc(epicPath.Mem(epicPathUb), R4)
		} else {
			rawPath := p.scionLayer.Path.(*scion.Raw)
			assert acc(path.Mem(ubPath), R4)
			assert acc(rawPath.Mem(ubPath), R4)
		}
		fold acc(p.scionLayer.Mem(ub), R4)
		@*/
		return nil, serrors.Wrap(cannotRoute, err, "details", "decoding raw path")
	}
	// @ ghost rawPath := path.RawBufferMem(ubPath)
	revPathTmp, err := decPath.Reverse( /*@ rawPath @*/ )
	if err != nil {
		/*@
		sl.CombineRange_Bytes(ub, startP, endP, writePerm)
		ghost if pathFromEpic {
			epicPath := p.scionLayer.Path.(*epic.Path)
			assert acc(path.Mem(ubPath), R4)
			fold acc(epicPath.Mem(epicPathUb), R4)
		} else {
			rawPath := p.scionLayer.Path.(*scion.Raw)
			assert acc(path.Mem(ubPath), R4)
			assert acc(rawPath.Mem(ubPath), R4)
		}
		fold acc(p.scionLayer.Mem(ub), R4)
		@*/
		return nil, serrors.Wrap(cannotRoute, err, "details", "reversing path for SCMP")
	}
	// @ assert revPathTmp.Mem(rawPath)
	revPath := revPathTmp.(*scion.Decoded)
	// @ assert revPath.Mem(rawPath)

	// Revert potential path segment switches that were done during processing.
	if revPath.IsXover( /*@ rawPath @*/ ) {
		if err := revPath.IncPath( /*@ rawPath @*/ ); err != nil {
			/*@
			sl.CombineRange_Bytes(ub, startP, endP, writePerm)
			ghost if pathFromEpic {
				epicPath := p.scionLayer.Path.(*epic.Path)
				assert acc(path.Mem(ubPath), R4)
				fold acc(epicPath.Mem(epicPathUb), R4)
			} else {
				rawPath := p.scionLayer.Path.(*scion.Raw)
				assert acc(path.Mem(ubPath), R4)
				assert acc(rawPath.Mem(ubPath), R4)
			}
			fold acc(p.scionLayer.Mem(ub), R4)
			@*/
			return nil, serrors.Wrap(cannotRoute, err, "details", "reverting cross over for SCMP")
		}
	}
	// If the packet is sent to an external router, we need to increment the
	// path to prepare it for the next hop.
	// @ p.d.getExternalMem()
	// @ if p.d.external != nil { unfold acc(accBatchConn(p.d.external), _) }
	_, external := p.d.external[p.ingressID]
	if external {
		// @ requires revPath.Mem(rawPath)
		// @ requires revPath.ValidCurrIdxs(rawPath)
		// @ ensures  revPath.Mem(rawPath)
		// @ decreases
		// @ outline(
		// @ unfold revPath.Mem(rawPath)
		// @ unfold revPath.Base.Mem()
		infoField := &revPath.InfoFields[revPath.PathMeta.CurrINF]
		if infoField.ConsDir {
			hopField := /*@ unfolding acc(revPath.HopFields[revPath.PathMeta.CurrHF].Mem(), _) in @*/
				revPath.HopFields[revPath.PathMeta.CurrHF]
			infoField.UpdateSegID(hopField.Mac)
		}
		// @ fold revPath.Base.Mem()
		// @ fold revPath.Mem(rawPath)
		// @ )
		if err := revPath.IncPath( /*@ rawPath @*/ ); err != nil {
			/*@
			sl.CombineRange_Bytes(ub, startP, endP, writePerm)
			ghost if pathFromEpic {
				epicPath := p.scionLayer.Path.(*epic.Path)
				assert acc(path.Mem(ubPath), R4)
				fold acc(epicPath.Mem(epicPathUb), R4)
			} else {
				rawPath := p.scionLayer.Path.(*scion.Raw)
				assert acc(path.Mem(ubPath), R4)
				assert acc(rawPath.Mem(ubPath), R4)
			}
			fold acc(p.scionLayer.Mem(ub), R4)
			@*/
			return nil, serrors.Wrap(cannotRoute, err, "details", "incrementing path for SCMP")
		}
	}
	// @ TODO()

	// create new SCION header for reply.
	var scionL /*@@@*/ slayers.SCION
	// (VerifiedSCION) TODO: adapt *SCION.Mem(...)
	scionL.FlowID = p.scionLayer.FlowID
	scionL.TrafficClass = p.scionLayer.TrafficClass
	scionL.PathType = revPath.Type( /*@ nil @*/ )
	scionL.Path = revPath
	scionL.DstIA = p.scionLayer.SrcIA
	scionL.SrcIA = p.d.localIA
	srcA, err := p.scionLayer.SrcAddr()
	if err != nil {
		return nil, serrors.Wrap(cannotRoute, err, "details", "extracting src addr")
	}
	if err := scionL.SetDstAddr(srcA /*@ , false @*/); err != nil {
		return nil, serrors.Wrap(cannotRoute, err, "details", "setting dest addr")
	}
	if err := scionL.SetSrcAddr(&net.IPAddr{IP: p.d.internalIP} /*@ , false @*/); err != nil {
		return nil, serrors.Wrap(cannotRoute, err, "details", "setting src addr")
	}
	scionL.NextHdr = slayers.L4SCMP

	typeCode := slayers.CreateSCMPTypeCode(typ, code)
	scmpH /*@@@*/ := slayers.SCMP{TypeCode: typeCode}
	scmpH.SetNetworkLayerForChecksum(&scionL)

	if err := p.buffer.Clear(); err != nil {
		return nil, err
	}

	sopts := gopacket.SerializeOptions{
		ComputeChecksums: true,
		FixLengths:       true,
	}
	scmpLayers := []gopacket.SerializableLayer{&scionL, &scmpH, scmpP}
	if cause != nil {
		// add quote for errors.
		hdrLen := slayers.CmnHdrLen + scionL.AddrHdrLen( /*@ nil, false @*/ ) + scionL.Path.Len( /*@ nil @*/ )
		switch scmpH.TypeCode.Type() {
		case slayers.SCMPTypeExternalInterfaceDown:
			hdrLen += 20
		case slayers.SCMPTypeInternalConnectivityDown:
			hdrLen += 28
		default:
			hdrLen += 8
		}
		quote := p.rawPkt
		maxQuoteLen := slayers.MaxSCMPPacketLen - hdrLen
		if len(quote) > maxQuoteLen {
			quote = quote[:maxQuoteLen]
		}
		scmpLayers = append( /*@ noPerm, @*/ scmpLayers, gopacket.Payload(quote))
	}
	// XXX(matzf) could we use iovec gather to avoid copying quote?
	err = gopacket.SerializeLayers(p.buffer, sopts /*@ , nil @*/, scmpLayers...)
	if err != nil {
		return nil, serrors.Wrap(cannotRoute, err, "details", "serializing SCMP message")
	}
	return p.buffer.Bytes(), scmpError{TypeCode: typeCode, Cause: cause}
}

// decodeLayers implements roughly the functionality of
// gopacket.DecodingLayerParser, but customized to our use case with a "base"
// layer and additional, optional layers in the given order.
// Returns the last decoded layer.
// @ requires  base != nil && base.NonInitMem()
// @ requires  forall i int :: { &opts[i] } 0 <= i && i < len(opts) ==>
// @     (acc(&opts[i], R10) && opts[i] != nil && opts[i].NonInitMem())
// Due to Viper's very strict injectivity constraints:
// @ requires  forall i, j int :: { &opts[i], &opts[j] } 0 <= i && i < j && j < len(opts) ==>
// @     opts[i] !== opts[j]
// @ preserves sl.AbsSlice_Bytes(data, 0, len(data))
// @ ensures   forall i int :: { &opts[i] } 0 <= i && i < len(opts) ==>
// @     (acc(&opts[i], R10) && opts[i] != nil)
// @ ensures   -1 <= idx && idx < len(opts)
// @ ensures   len(processed) == len(opts)
// @ ensures   len(offsets) == len(opts)
// @ ensures   reterr == nil && 0  <= idx ==> processed[idx]
// @ ensures   reterr == nil && idx == -1  ==> retl === base
// @ ensures   reterr == nil && 0   <= idx ==> retl === opts[idx]
// @ ensures   reterr == nil ==> retl != nil
// @ ensures   reterr == nil ==> base.Mem(data)
// @ ensures   forall i int :: {&opts[i]}{processed[i]} 0 <= i && i < len(opts) ==>
// @     (processed[i] ==> (0 <= offsets[i].start && offsets[i].start <= offsets[i].end && offsets[i].end <= len(data)))
// @ ensures   reterr == nil ==> forall i int :: {&opts[i]}{processed[i]} 0 <= i && i < len(opts) ==>
// @     ((processed[i] && !offsets[i].isNil) ==> opts[i].Mem(data[offsets[i].start:offsets[i].end]))
// @ ensures   reterr == nil ==> forall i int :: {&opts[i]}{processed[i]} 0 <= i && i < len(opts) ==>
// @     ((processed[i] && offsets[i].isNil) ==> opts[i].Mem(nil))
// @ ensures   reterr == nil ==> forall i int :: {&opts[i]}{processed[i]} 0 <= i && i < len(opts) ==>
// @     (!processed[i] ==> opts[i].NonInitMem())
// @ ensures   reterr != nil ==> base.NonInitMem()
// @ ensures   reterr != nil ==> (forall i int :: { &opts[i] } 0 <= i && i < len(opts) ==> opts[i].NonInitMem())
// @ ensures   reterr != nil ==> reterr.ErrorMem()
// @ decreases
func decodeLayers(data []byte, base gopacket.DecodingLayer,
	opts ...gopacket.DecodingLayer) (retl gopacket.DecodingLayer, reterr error /*@ , ghost processed seq[bool], ghost offsets seq[offsetPair], ghost idx int @*/) {

	// @ processed = seqs.NewSeqBool(len(opts))
	// @ offsets = newOffsetPair(len(opts))
	// @ idx = -1
	// @ gopacket.AssertInvariantNilDecodeFeedback()
	if err := base.DecodeFromBytes(data, gopacket.NilDecodeFeedback); err != nil {
		return nil, err /*@ , processed, offsets, idx @*/
	}
	last := base
	optsSlice := ([](gopacket.DecodingLayer))(opts)

	// @ ghost oldData := data
	// @ ghost oldStart := 0
	// @ ghost oldEnd := len(data)

	// @ invariant sl.AbsSlice_Bytes(oldData, 0, len(oldData))
	// @ invariant base.Mem(oldData)
	// @ invariant 0 < len(opts) ==> 0 <= i0 && i0 <= len(opts)
	// @ invariant forall i int :: {&opts[i]} 0 <= i && i < len(opts) ==> acc(&opts[i], R10)
	// @ invariant forall i, j int :: {&opts[i], &opts[j]} 0 <= i && i < j && j < len(opts) ==> opts[i] !== opts[j]
	// @ invariant forall i int :: {&opts[i]} 0 <= i && i < len(opts) ==> opts[i] != nil
	// @ invariant len(processed) == len(opts)
	// @ invariant len(offsets) == len(opts)
	// @ invariant -1 <= idx && idx < len(opts)
	// @ invariant idx == -1 ==> (last === base && oldStart == 0 && oldEnd == len(oldData))
	// @ invariant 0 <= idx ==> (processed[idx] && last === opts[idx])
	// @ invariant forall i int :: {&opts[i]}{processed[i]} 0 <= i && i < len(opts) ==>
	// @     (processed[i] ==> (0 <= offsets[i].start && offsets[i].start <= offsets[i].end && offsets[i].end <= len(data)))
	// @ invariant forall i int :: {&opts[i]}{processed[i]} 0 <= i && i < len(opts) ==>
	// @     ((processed[i] && !offsets[i].isNil) ==> opts[i].Mem(oldData[offsets[i].start:offsets[i].end]))
	// @ invariant forall i int :: {&opts[i]}{processed[i]} 0 <= i && i < len(opts) ==>
	// @     ((processed[i] && offsets[i].isNil) ==> opts[i].Mem(nil))
	// @ invariant forall i int :: {&opts[i]}{processed[i]} 0 < len(opts) && i0 <= i && i < len(opts) ==>
	// @     !processed[i]
	// @ invariant forall i int :: {&opts[i]}{processed[i]} 0 <= i && i < len(opts) ==>
	// @     (!processed[i] ==> opts[i].NonInitMem())
	// @ invariant gopacket.NilDecodeFeedback.Mem()
	// @ invariant 0 <= oldStart && oldStart <= oldEnd && oldEnd <= len(oldData)
	// @ decreases len(opts) - i0
	for _, opt := range optsSlice /*@ with i0 @*/ {
		layerClassTmp := opt.CanDecode()
		// @ fold layerClassTmp.Mem()
		// @ ghost var pos offsetPair
		// @ ghost var ub []byte
		// @ ghost if idx == -1 {
		// @     pos = offsetPair{0, len(oldData), false}
		// @     ub = oldData
		// @ } else {
		// @     pos = offsets[idx]
		// @     if pos.isNil { ub = nil } else { ub  = oldData[pos.start:pos.end] }
		// @ }
		if layerClassTmp.Contains(last.NextLayerType( /*@ ub @*/ )) {
			data /*@ , start, end @*/ := last.LayerPayload( /*@ ub @*/ )
			// @ assert data == nil || data === oldData[pos.start:pos.end][start:end]
			// @ oldEnd   = pos.start + end
			// @ oldStart = pos.start + start
			// @ ghost if data == nil {
			// @ 	sl.NilAcc_Bytes()
			// @ } else {
			// @	sl.SplitRange_Bytes(oldData, oldStart, oldEnd, writePerm)
			// @ }
			if err := opt.DecodeFromBytes(data, gopacket.NilDecodeFeedback); err != nil {
				// @ ghost if data != nil { sl.CombineRange_Bytes(oldData, oldStart, oldEnd, writePerm) }
				// @ base.DowngradePerm(oldData)

				// ghost clean-up:
				// @ ghost
				// @ invariant 0 <= i0 && i0 <= len(opts)
				// @ invariant -1 <= c && c <= i0
				// @ invariant len(processed) == len(opts)
				// @ invariant len(offsets) == len(opts)
				// @ invariant forall i int :: {&opts[i]} 0 <= i && i < len(opts) ==> acc(&opts[i], R10)
				// @ invariant forall i, j int :: {&opts[i], &opts[j]} 0 <= i && i < j && j < len(opts) ==> opts[i] !== opts[j]
				// @ invariant forall i int :: {&opts[i]} 0 <= i && i < len(opts) ==> opts[i] != nil
				// @ invariant forall i int :: {&opts[i]}{processed[i]} 0 <= i && i < len(opts) ==>
				// @     (processed[i] ==> (0 <= offsets[i].start && offsets[i].start <= offsets[i].end && offsets[i].end <= len(oldData)))
				// @ invariant forall i int :: {&opts[i]}{processed[i]} 0 <= i && i < len(opts) ==>
				// @     ((processed[i] && !offsets[i].isNil) ==> opts[i].Mem(oldData[offsets[i].start:offsets[i].end]))
				// @ invariant forall i int :: {&opts[i]}{processed[i]} 0 <= i && i < len(opts) ==>
				// @     ((processed[i] && offsets[i].isNil) ==> opts[i].Mem(nil))
				// @ invariant forall i int :: {&opts[i]}{processed[i]} 0 <= i && i < len(opts) ==>
				// @     (!processed[i] ==> opts[i].NonInitMem())
				// @ invariant forall i int :: {&opts[i]}{processed[i]} 0 < len(opts) && c < i && i < len(opts) ==>
				// @     !processed[i]
				// @ decreases c
				// @ for c := i0-1; 0 <= c; c=c-1 {
				// @	if processed[c] {
				// @		off := offsets[c]
				// @        if off.isNil {
				// @ 			opts[c].DowngradePerm(nil)
				// @		} else {
				// @ 			opts[c].DowngradePerm(oldData[off.start:off.end])
				// @ 		}
				// @ 	}
				// @ 	processed[c] = false
				// @ }
				return nil, err /*@, processed, offsets, idx @*/
			}
			// @ processed[i0] = true
			// @ ghost offsets[i0] = offsetPair{oldStart, oldEnd, data == nil}
			// @ idx = i0
			// @ ghost if data != nil { sl.CombineRange_Bytes(oldData, oldStart, oldEnd, writePerm) }
			last = opt
		}
	}
	return last, nil /*@ , processed, offsets, idx @*/
}

// @ preserves acc(layer.Mem(ubuf), R20)
// @ decreases
func nextHdr(layer gopacket.DecodingLayer /*@ , ghost ubuf []byte @*/) slayers.L4ProtocolType {
	switch v := layer.(type) {
	case *slayers.SCION:
		return /*@ unfolding acc(v.Mem(ubuf), R20) in @*/ v.NextHdr
	case *slayers.EndToEndExtnSkipper:
		return /*@ unfolding acc(v.Mem(ubuf), R20) in (unfolding acc(v.extnBase.Mem(ubuf), R20) in @*/ v.NextHdr /*@ ) @*/
	case *slayers.HopByHopExtnSkipper:
		return /*@ unfolding acc(v.Mem(ubuf), R20) in (unfolding acc(v.extnBase.Mem(ubuf), R20) in @*/ v.NextHdr /*@ ) @*/
	default:
		return slayers.L4None
	}
}

// forwardingMetrics contains the subset of Metrics relevant for forwarding,
// instantiated with some interface-specific labels.
type forwardingMetrics struct {
	InputBytesTotal     prometheus.Counter
	OutputBytesTotal    prometheus.Counter
	InputPacketsTotal   prometheus.Counter
	OutputPacketsTotal  prometheus.Counter
	DroppedPacketsTotal prometheus.Counter
}

// @ requires  acc(labels, _)
// @ preserves acc(metrics.Mem(), _)
// @ ensures   acc(forwardingMetricsNonInjectiveMem(res), _)
// @ decreases
func initForwardingMetrics(metrics *Metrics, labels prometheus.Labels) (res forwardingMetrics) {
	// @ unfold acc(metrics.Mem(), _)
	c := forwardingMetrics{
		InputBytesTotal:     metrics.InputBytesTotal.With(labels),
		InputPacketsTotal:   metrics.InputPacketsTotal.With(labels),
		OutputBytesTotal:    metrics.OutputBytesTotal.With(labels),
		OutputPacketsTotal:  metrics.OutputPacketsTotal.With(labels),
		DroppedPacketsTotal: metrics.DroppedPacketsTotal.With(labels),
	}
	c.InputBytesTotal.Add(float64(0))
	c.InputPacketsTotal.Add(float64(0))
	c.OutputBytesTotal.Add(float64(0))
	c.OutputPacketsTotal.Add(float64(0))
	c.DroppedPacketsTotal.Add(float64(0))
	// @ fold acc(forwardingMetricsNonInjectiveMem(c), _)
	return c
}

// @ preserves neighbors != nil ==> acc(neighbors, R20)
// @ ensures   acc(res)
// @ decreases
func interfaceToMetricLabels(id uint16, localIA addr.IA,
	neighbors map[uint16]addr.IA) (res prometheus.Labels) {
	// (VerifiedSCION) Gobra cannot prove this, even though it is obvious from the
	// type of id.
	// @ assume 0 <= id

	if id == 0 {
		return prometheus.Labels{
			"isd_as":          localIA.String(),
			"interface":       "internal",
			"neighbor_isd_as": localIA.String(),
		}
	}
	return prometheus.Labels{
		"isd_as":          localIA.String(),
		"interface":       strconv.FormatUint(uint64(id), 10),
		"neighbor_isd_as": neighbors[id].String(),
	}
}

// @ ensures acc(res)
// @ decreases
func serviceMetricLabels(localIA addr.IA, svc addr.HostSVC) (res prometheus.Labels) {
	return prometheus.Labels{
		"isd_as":  localIA.String(),
		"service": svc.BaseString(),
	}
}
