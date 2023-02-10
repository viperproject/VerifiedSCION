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

// (VerifiedSCION) Uncommenting the following causes severe slowdowns, but it verifies
// initEnsures alreadySet                    != nil && alreadySet.ErrorMem()
// initEnsures cannotRoute                   != nil && cannotRoute.ErrorMem()
// initEnsures emptyValue                    != nil && emptyValue.ErrorMem()
// initEnsures malformedPath                 != nil && malformedPath.ErrorMem()
// initEnsures modifyExisting                != nil && modifyExisting.ErrorMem()
// initEnsures noSVCBackend                  != nil && noSVCBackend.ErrorMem()
// initEnsures unsupportedPathType           != nil && unsupportedPathType.ErrorMem()
// initEnsures unsupportedPathTypeNextHeader != nil && unsupportedPathTypeNextHeader.ErrorMem()
// initEnsures noBFDSessionFound             != nil && noBFDSessionFound.ErrorMem()
// initEnsures noBFDSessionConfigured        != nil && noBFDSessionConfigured.ErrorMem()
// initEnsures errBFDDisabled                != nil && errBFDDisabled.ErrorMem()
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
	// @ def "github.com/scionproto/scion/verification/utils/definitions"
	// @ "github.com/scionproto/scion/verification/utils/slices"
	// @ sl "github.com/scionproto/scion/verification/utils/slices"
	// @ "github.com/scionproto/scion/verification/utils/seqs"
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

	// (VerifiedSCION) ctx is used to obtain a logger from ctx by
	// calling the method Value. ReadL20 permissions are enough for that.
	// @ requires acc(ctx.Mem(), def.ReadL20)
	// @ requires acc(Mem(), _)
	// @ ensures  err != nil ==> err.ErrorMem()
	Run(ctx context.Context) (err error)
	// @ requires acc(Mem(), _)
	// @ requires msg.Mem(ub)
	ReceiveMessage(msg *layers.BFD /*@ , ghost ub []byte @*/)
	// @ requires acc(Mem(), _)
	IsUp() bool
}

// BatchConn is a connection that supports batch reads and writes.
// (VerifiedSCION) the spec of this interface exactly matches that of the same methods
// in private/underlay/conn/Conn
type BatchConn interface {
	// @ pred Mem()

	// @ preserves Mem()
	// @ preserves forall i int :: 0 <= i && i < len(msgs) ==> msgs[i].Mem(1)
	// @ ensures   err == nil ==> 0 <= n && n <= len(msgs)
	// @ ensures   err != nil ==> err.ErrorMem()
	ReadBatch(msgs underlayconn.Messages) (n int, err error)
	// @ requires  acc(addr.Mem(), _)
	// @ preserves Mem()
	// @ preserves acc(slices.AbsSlice_Bytes(b, 0, len(b)), def.ReadL10)
	// @ ensures   err == nil ==> 0 <= n && n <= len(b)
	// @ ensures   err != nil ==> err.ErrorMem()
	WriteTo(b []byte, addr *net.UDPAddr) (n int, err error)
	// @ preserves Mem()
	// @ preserves forall i int :: 0 <= i && i < len(msgs) ==> acc(msgs[i].Mem(1), def.ReadL10)
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

// @ preserves e.ErrorMem()
// (VerifiedSCION): Gobra can't prove termination here because we call Error
// to the result of New and right now it is not able to prove that this will
// not be a new scmpError. We assume it.
// @ decreases _
func (e scmpError) Error() string {
	// @ unfold e.ErrorMem()
	// @ defer fold e.ErrorMem()
	return serrors.New("scmp", "typecode", e.TypeCode, "cause", e.Cause).Error()
}

// SetIA sets the local IA for the dataplane.
// @ requires  acc(&d.running, 1/2) && !d.running
// @ requires  acc(&d.localIA, 1/2) && d.localIA.IsZero()
// @ requires  !ia.IsZero()
// @ preserves d.mtx.LockP()
// @ preserves d.mtx.LockInv() == MutexInvariant!<d!>;
// @ ensures   acc(&d.running, 1/2) && !d.running
// @ ensures   acc(&d.localIA, 1/2)
// @ ensures   e == nil
func (d *DataPlane) SetIA(ia addr.IA) (e error) {
	d.mtx.Lock()
	defer d.mtx.Unlock()
	// @ unfold MutexInvariant!<d!>()
	// @ defer fold MutexInvariant!<d!>()
	if d.running {
		return modifyExisting
	}
	if ia.IsZero() {
		return emptyValue
	}
	if !d.localIA.IsZero() {
		return alreadySet
	}
	d.localIA = ia
	return nil
}

// SetKey sets the key used for MAC verification. The key provided here should
// already be derived as in scrypto.HFMacFactory.
// @ requires  acc(&d.key,        1/2)
// @ requires  acc(d.key,         1/2)
// @ requires  acc(&d.running,    1/2) && !d.running
// @ requires  acc(&d.macFactory, 1/2) && d.macFactory == nil
// @ requires  len(key) > 0
// @ requires  slices.AbsSlice_Bytes(key, 0, len(key))
// @ preserves d.mtx.LockP()
// @ preserves d.mtx.LockInv() == MutexInvariant!<d!>;
// @ ensures   acc(&d.running,    1/2) && !d.running
// @ ensures   res == nil ==> d.MacFactoryOperational()
func (d *DataPlane) SetKey(key []byte) (res error) {
	// @ share key
	d.mtx.Lock()
	defer d.mtx.Unlock()
	// @ unfold MutexInvariant!<d!>()
	// @ defer fold MutexInvariant!<d!>()
	if d.running {
		// @ def.Unreachable()
		return modifyExisting
	}
	if len(key) == 0 {
		// @ def.Unreachable()
		return emptyValue
	}
	if d.macFactory != nil {
		// @ def.Unreachable()
		return alreadySet
	}
	// First check for MAC creation errors.
	if _, err := scrypto.InitMac(key); err != nil {
		return err
	}
	// @ d.key = &key
	verScionTemp :=
		// @ requires acc(&key, _) && acc(slices.AbsSlice_Bytes(key, 0, len(key)), _)
		// @ requires scrypto.ValidKeyForHash(key)
		// @ ensures  acc(&key, _) && acc(slices.AbsSlice_Bytes(key, 0, len(key)), _)
		// @ ensures  h.Mem()
		// @ decreases
		func /*@ f @*/ () (h hash.Hash) {
			mac, _ := scrypto.InitMac(key)
			return mac
		}
	// @ proof verScionTemp implements MacFactorySpec{d.key} {
	// @   return verScionTemp() as f
	// @ }
	d.macFactory = verScionTemp
	// @ fold d.MacFactoryOperational()
	return nil
}

// AddInternalInterface sets the interface the data-plane will use to
// send/receive traffic in the local AS. This can only be called once; future
// calls will return an error. This can only be called on a not yet running
// dataplane.
// @ requires  acc(&d.running,    1/2) && !d.running
// @ requires  acc(&d.internal,   1/2) && d.internal == nil
// @ requires  acc(&d.internalIP, 1/2)
// @ requires  conn != nil && conn.Mem()
// @ requires  ip.Mem()
// @ preserves d.mtx.LockP()
// @ preserves d.mtx.LockInv() == MutexInvariant!<d!>;
// @ ensures   acc(&d.running,    1/2) && !d.running
// @ ensures   acc(&d.internal,   1/2)
// @ ensures   acc(&d.internalIP, 1/2)
func (d *DataPlane) AddInternalInterface(conn BatchConn, ip net.IP) error {
	d.mtx.Lock()
	defer d.mtx.Unlock()
	// @ unfold MutexInvariant!<d!>()
	// @ defer fold MutexInvariant!<d!>()
	if d.running {
		return modifyExisting
	}
	if conn == nil {
		return emptyValue
	}
	if d.internal != nil {
		return alreadySet
	}
	d.internal = conn
	d.internalIP = ip
	return nil
}

// AddExternalInterface adds the inter AS connection for the given interface ID.
// If a connection for the given ID is already set this method will return an
// error. This can only be called on a not yet running dataplane.
// @ requires  acc(&d.running,    1/2) && !d.running
// @ requires  acc(&d.external,   1/2)
// @ requires  d.external != nil ==> acc(d.external, 1/2)
// @ requires  !(ifID in domain(d.external))
// @ requires  conn != nil && conn.Mem()
// @ preserves d.mtx.LockP()
// @ preserves d.mtx.LockInv() == MutexInvariant!<d!>;
// @ ensures   acc(&d.running,    1/2) && !d.running
// @ ensures   acc(&d.external,   1/2) && acc(d.external, 1/2)
func (d *DataPlane) AddExternalInterface(ifID uint16, conn BatchConn) error {
	d.mtx.Lock()
	defer d.mtx.Unlock()
	// @ unfold MutexInvariant!<d!>()
	// @ defer fold MutexInvariant!<d!>()
	if d.running {
		return modifyExisting
	}
	if conn == nil {
		return emptyValue
	}
	if _, existsB := d.external[ifID]; existsB {
		return serrors.WithCtx(alreadySet, "ifID", ifID)
	}
	if d.external == nil {
		d.external = make(map[uint16]BatchConn)
		// @ fold AccBatchConn(d.external)
	}
	// @ unfold AccBatchConn(d.external)
	d.external[ifID] = conn
	// @ fold AccBatchConn(d.external)
	return nil
}

// AddNeighborIA adds the neighboring IA for a given interface ID. If an IA for
// the given ID is already set, this method will return an error. This can only
// be called on a yet running dataplane.
// @ requires  acc(&d.running,     1/2) && !d.running
// @ requires  acc(&d.neighborIAs, 1/2)
// @ requires  d.neighborIAs != nil ==> acc(d.neighborIAs, 1/2)
// @ requires  !remote.IsZero()
// @ requires  !(ifID in domain(d.neighborIAs))
// @ preserves d.mtx.LockP()
// @ preserves d.mtx.LockInv() == MutexInvariant!<d!>;
// @ ensures   acc(&d.running,    1/2) && !d.running
// @ ensures   acc(&d.neighborIAs,1/2) && acc(d.neighborIAs, 1/2)
// @ ensures   domain(d.neighborIAs) == old(domain(d.neighborIAs)) union set[uint16]{ifID}
func (d *DataPlane) AddNeighborIA(ifID uint16, remote addr.IA) error {
	d.mtx.Lock()
	defer d.mtx.Unlock()
	// @ unfold MutexInvariant!<d!>()
	// @ defer fold MutexInvariant!<d!>()
	if d.running {
		return modifyExisting
	}
	if remote.IsZero() {
		return emptyValue
	}
	if _, existsB := d.neighborIAs[ifID]; existsB {
		return serrors.WithCtx(alreadySet, "ifID", ifID)
	}
	if d.neighborIAs == nil {
		d.neighborIAs = make(map[uint16]addr.IA)
	}
	d.neighborIAs[ifID] = remote
	return nil
}

// AddLinkType adds the link type for a given interface ID. If a link type for
// the given ID is already set, this method will return an error. This can only
// be called on a not yet running dataplane.
// @ requires  acc(&d.running,   1/2) && !d.running
// @ requires  acc(&d.linkTypes, 1/2)
// @ requires  d.linkTypes != nil ==> acc(d.linkTypes, 1/2)
// @ requires  !(ifID in domain(d.linkTypes))
// (VerifiedSCION) unlike all other setter methods, this does not lock
// d.mtx. Did the devs forget about it?
// @ preserves MutexInvariant!<d!>()
// @ ensures   acc(&d.running,   1/2) && !d.running
// @ ensures   acc(&d.linkTypes, 1/2) && acc(d.linkTypes, 1/2)
// @ ensures   domain(d.linkTypes) == old(domain(d.linkTypes)) union set[uint16]{ifID}
func (d *DataPlane) AddLinkType(ifID uint16, linkTo topology.LinkType) error {
	if _, existsB := d.linkTypes[ifID]; existsB {
		return serrors.WithCtx(alreadySet, "ifID", ifID)
	}
	// @ unfold MutexInvariant!<d!>()
	// @ defer fold MutexInvariant!<d!>()
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
// @ preserves acc(MutexInvariant!<d!>(), def.ReadL5)
func (d *DataPlane) getInterfaceState(interfaceID uint16) control.InterfaceState {
	// @ unfold acc(MutexInvariant!<d!>(), def.ReadL5)
	// @ defer fold acc(MutexInvariant!<d!>(), def.ReadL5)
	bfdSessions := d.bfdSessions
	// @ ghost if bfdSessions != nil {
	// @		unfold acc(AccBfdSession(d.bfdSessions), def.ReadL20)
	// @		defer fold acc(AccBfdSession(d.bfdSessions), def.ReadL20)
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
// @ requires  acc(metrics.PacketsSent.Mem(), _) && acc(metrics.PacketsReceived.Mem(), _)
// @ requires  acc(metrics.Up.Mem(), _) && acc(metrics.StateChanges.Mem(), _)
// @ preserves MutexInvariant!<d!>()
// @ requires  s.Mem()
// @ decreases
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
// @ requires  a != nil && acc(a.Mem(), def.ReadL10)
// @ preserves acc(&d.svc, 1/2)
// @ preserves d.mtx.LockP()
// @ preserves d.mtx.LockInv() == MutexInvariant!<d!>;
func (d *DataPlane) AddSvc(svc addr.HostSVC, a *net.UDPAddr) error {
	d.mtx.Lock()
	defer d.mtx.Unlock()
	if a == nil {
		return emptyValue
	}
	// @ preserves MutexInvariant!<d!>()
	// @ preserves acc(&d.svc, 1/2)
	// @ ensures   d.svc != nil && acc(d.svc.Mem(), _)
	// @ decreases
	// @ outline(
	// @ unfold MutexInvariant!<d!>()
	if d.svc == nil {
		d.svc = newServices()
	}
	// @ fold MutexInvariant!<d!>()
	// @ )
	// @ unfold acc(MutexInvariant!<d!>(), def.ReadL15)
	// @ assert acc(d.svc.Mem(), _)
	d.svc.AddSvc(svc, a)
	if d.Metrics != nil {
		labels := serviceMetricLabels(d.localIA, svc)
		// @ requires acc(&d.Metrics, def.ReadL20)
		// @ requires acc(d.Metrics.Mem(), _)
		// @ requires acc(labels, _)
		// @ ensures  acc(&d.Metrics, def.ReadL20)
		// @ decreases
		// @ outline (
		// @ unfold acc(d.Metrics.Mem(), _)
		// @ assume float64(0) < float64(1) // Gobra still does not fully support floats
		// @ assert d.Metrics.ServiceInstanceChanges != nil
		// @ assert d.Metrics.ServiceInstanceCount   != nil
		d.Metrics.ServiceInstanceChanges.With(labels).Add(float64(1))
		d.Metrics.ServiceInstanceCount.With(labels).Add(float64(1))
		// @ )
	}
	// @ fold acc(MutexInvariant!<d!>(), def.ReadL15)
	return nil
}

// DelSvc deletes the address for the given service.
// @ requires  a != nil && acc(a.Mem(), def.ReadL10)
// @ preserves d.mtx.LockP()
// @ preserves d.mtx.LockInv() == MutexInvariant!<d!>;
func (d *DataPlane) DelSvc(svc addr.HostSVC, a *net.UDPAddr) error {
	d.mtx.Lock()
	defer d.mtx.Unlock()
	if a == nil {
		return emptyValue
	}
	// @ unfold acc(MutexInvariant!<d!>(), def.ReadL15)
	// @ ghost defer fold acc(MutexInvariant!<d!>(), def.ReadL15)
	if d.svc == nil {
		return nil
	}
	d.svc.DelSvc(svc, a)
	if d.Metrics != nil {
		labels := serviceMetricLabels(d.localIA, svc)
		// @ unfold acc(d.Metrics.Mem(), _)
		// @ assume float64(0) < float64(1) // Gobra still does not fully support floats
		d.Metrics.ServiceInstanceChanges.With(labels).Add(float64(1))
		d.Metrics.ServiceInstanceCount.With(labels).Add(float64(-1))
	}
	return nil
}

// AddNextHop sets the next hop address for the given interface ID. If the
// interface ID already has an address associated this operation fails. This can
// only be called on a not yet running dataplane.
// @ requires  acc(&d.running,          1/2) && !d.running
// @ requires  acc(&d.internalNextHops, 1/2)
// @ requires  d.internalNextHops != nil ==> acc(d.internalNextHops, 1/2)
// @ requires  !(ifID in domain(d.internalNextHops))
// @ requires  a != nil && acc(a.Mem(), _)
// @ preserves d.mtx.LockP()
// @ preserves d.mtx.LockInv() == MutexInvariant!<d!>;
// @ ensures   acc(&d.running,          1/2) && !d.running
// @ ensures   acc(&d.internalNextHops, 1/2) && acc(d.internalNextHops, 1/2)
func (d *DataPlane) AddNextHop(ifID uint16, a *net.UDPAddr) error {
	d.mtx.Lock()
	defer d.mtx.Unlock()
	// @ unfold MutexInvariant!<d!>()
	// @ defer fold MutexInvariant!<d!>()
	if d.running {
		return modifyExisting
	}
	if a == nil {
		return emptyValue
	}
	if _, existsB := d.internalNextHops[ifID]; existsB {
		return serrors.WithCtx(alreadySet, "ifID", ifID)
	}
	if d.internalNextHops == nil {
		d.internalNextHops = make(map[uint16]*net.UDPAddr)
		// @ fold AccAddr(d.internalNextHops)
	}
	// @ unfold AccAddr(d.internalNextHops)
	// @ defer fold AccAddr(d.internalNextHops)
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
// @ trusted
// @ requires false
func (d *DataPlane) Run(ctx context.Context) error {
	d.mtx.Lock()
	d.running = true

	// (VerifiedSCION) TODO: change the invariant to have the resources only
	//     when it is not runnning. That way, we can unfold the memory predicate
	//     right after setting running to true, which is required for the call to unlock
	//     to succeed. the rest of the permissions will be held in the closure footprint
	//     and on this method.
	d.initMetrics()

	read := func(ingressID uint16, rd BatchConn) {

		msgs := conn.NewReadMessages(inputBatchCnt)
		for _, msg := range msgs {
			msg.Buffers[0] = make([]byte, bufSize)
		}
		writeMsgs := make(underlayconn.Messages, 1)
		writeMsgs[0].Buffers = make([][]byte, 1)

		processor := newPacketProcessor(d, ingressID)
		var scmpErr scmpError
		for d.running {
			pkts, err := rd.ReadBatch(msgs)
			if err != nil {
				log.Debug("Failed to read batch", "err", err)
				// error metric
				continue
			}
			if pkts == 0 {
				continue
			}
			for _, p := range msgs[:pkts] {
				// input metric
				inputCounters := d.forwardingMetrics[ingressID]
				inputCounters.InputPacketsTotal.Inc()
				inputCounters.InputBytesTotal.Add(float64(p.N))

				srcAddr := p.Addr.(*net.UDPAddr)
				result, err := processor.processPkt(p.Buffers[0][:p.N], srcAddr)

				switch {
				case err == nil:
				case errors.As(err, &scmpErr):
					if !scmpErr.TypeCode.InfoMsg() {
						log.Debug("SCMP", "err", scmpErr, "dst_addr", p.Addr)
					}
					// SCMP go back the way they came.
					result.OutAddr = srcAddr
					result.OutConn = rd
				default:
					log.Debug("Error processing packet", "err", err)
					inputCounters.DroppedPacketsTotal.Inc()
					continue
				}
				if result.OutConn == nil { // e.g. BFD case no message is forwarded
					continue
				}

				// Write to OutConn; drop the packet if this would block.
				// Use WriteBatch because it's the only available function that
				// supports MSG_DONTWAIT.
				writeMsgs[0].Buffers[0] = result.OutPkt
				writeMsgs[0].Addr = nil
				if result.OutAddr != nil { // don't assign directly to net.Addr, typed nil!
					writeMsgs[0].Addr = result.OutAddr
				}

				_, err = result.OutConn.WriteBatch(writeMsgs, syscall.MSG_DONTWAIT)
				if err != nil {
					var errno syscall.Errno
					if !errors.As(err, &errno) ||
						!(errno == syscall.EAGAIN || errno == syscall.EWOULDBLOCK) {
						log.Debug("Error writing packet", "err", err)
						// error metric
					}
					inputCounters.DroppedPacketsTotal.Inc()
					continue
				}
				// ok metric
				outputCounters := d.forwardingMetrics[result.EgressID]
				outputCounters.OutputPacketsTotal.Inc()
				outputCounters.OutputBytesTotal.Add(float64(len(result.OutPkt)))
			}
		}
	}

	for k, v := range d.bfdSessions {
		go func(ifID uint16, c bfdSession) {
			defer log.HandlePanic()
			if err := c.Run(ctx); err != nil && err != bfd.AlreadyRunning {
				log.Error("BFD session failed to start", "ifID", ifID, "err", err)
			}
		}(k, v)
	}
	for ifID, v := range d.external {
		go func(i uint16, c BatchConn) {
			defer log.HandlePanic()
			read(i, c)
		}(ifID, v)
	}
	go func(c BatchConn) {
		defer log.HandlePanic()
		read(0, c)
	}(d.internal)

	d.mtx.Unlock()

	<-ctx.Done()
	return nil
}

// initMetrics initializes the metrics related to packet forwarding. The
// counters are already instantiated for all the relevant interfaces so this
// will not have to be repeated during packet forwarding.
// @ preserves acc(&d.forwardingMetrics)
// @ preserves acc(&d.localIA, def.ReadL15)
// @ preserves acc(&d.neighborIAs, def.ReadL15)
// @ preserves d.neighborIAs != nil ==> acc(d.neighborIAs, def.ReadL15) // required for call
// @ preserves acc(&d.Metrics, def.ReadL15) && acc(d.Metrics.Mem(), _)
// @ preserves acc(&d.external, def.ReadL15)
// @ preserves d.external != nil ==> acc(AccBatchConn(d.external), def.ReadL15) // required for call
// @ preserves acc(&d.internalNextHops, def.ReadL15)
// @ preserves d.internalNextHops != nil ==> acc(AccAddr(d.internalNextHops), def.ReadL15)
// @ ensures   AccForwardingMetrics(d.forwardingMetrics)
// @ decreases
func (d *DataPlane) initMetrics() {
	// @ preserves acc(&d.forwardingMetrics)
	// @ preserves acc(&d.localIA, def.ReadL20)
	// @ preserves acc(&d.neighborIAs, def.ReadL20)
	// @ preserves d.neighborIAs != nil ==> acc(d.neighborIAs, def.ReadL20)
	// @ preserves acc(&d.Metrics, def.ReadL20)
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
	// @ ghost if d.external != nil { unfold acc(AccBatchConn(d.external), def.ReadL15) }

	// @ fold acc(hideLocalIA(&d.localIA), def.ReadL15)

	// @ invariant acc(hideLocalIA(&d.localIA), def.ReadL15) // avoids incompletnes when folding acc(forwardingMetricsMem(d.forwardingMetrics[id], id), _)
	// @ invariant acc(&d.external, def.ReadL15)
	// @ invariant d.external != nil ==> acc(d.external, def.ReadL20)
	// @ invariant d.external === old(d.external)
	// @ invariant acc(&d.forwardingMetrics) && acc(d.forwardingMetrics)
	// @ invariant acc(&d.internalNextHops, def.ReadL15)
	// @ invariant d.internalNextHops === old(d.internalNextHops)
	// @ invariant d.internalNextHops != nil ==> acc(AccAddr(d.internalNextHops), def.ReadL15)
	// @ invariant acc(&d.neighborIAs, def.ReadL15)
	// @ invariant d.neighborIAs != nil ==> acc(d.neighborIAs, def.ReadL15)
	// @ invariant forall i uint16 :: { d.forwardingMetrics[i] } i in domain(d.forwardingMetrics) ==>
	// @ 	acc(forwardingMetricsMem(d.forwardingMetrics[i], i), _)
	// @ invariant acc(&d.Metrics, def.ReadL15)
	// @ invariant acc(d.Metrics.Mem(), _)
	// @ decreases len(d.external) - len(visitedSet)
	for id := range d.external /*@ with visitedSet @*/ {
		// @ ghost if d.internalNextHops != nil {
		// @	unfold acc(AccAddr(d.internalNextHops), def.ReadL20)
		// @ }
		if _, notOwned := d.internalNextHops[id]; notOwned {
			// @ ghost if d.internalNextHops != nil {
			// @ 	fold acc(AccAddr(d.internalNextHops), def.ReadL20)
			// @ }
			continue
		}
		// @ ghost if d.internalNextHops != nil {
		// @ 	fold acc(AccAddr(d.internalNextHops), def.ReadL20)
		// @ }
		labels = interfaceToMetricLabels(id, ( /*@ unfolding acc(hideLocalIA(&d.localIA), def.ReadL20) in @*/ d.localIA), d.neighborIAs)
		d.forwardingMetrics[id] = initForwardingMetrics(d.Metrics, labels)
		// @ liftForwardingMetricsNonInjectiveMem(d.forwardingMetrics[id], id)
		// @ assert acc(forwardingMetricsMem(d.forwardingMetrics[id], id), _)
	}
	// @ ghost if d.external != nil { fold acc(AccBatchConn(d.external), def.ReadL15) }
	// @ fold AccForwardingMetrics(d.forwardingMetrics)
	// @ unfold acc(hideLocalIA(&d.localIA), def.ReadL15)
}

type processResult struct {
	EgressID uint16
	OutConn  BatchConn
	OutAddr  *net.UDPAddr
	OutPkt   []byte
}

// @ requires  acc(d.MacFactoryOperational(), _)
// @ ensures   res.initMem()
// @ decreases
func newPacketProcessor(d *DataPlane, ingressID uint16) (res *scionPacketProcessor) {
	var verScionTmp gopacket.SerializeBuffer
	// @ unfold acc(d.MacFactoryOperational(), _)
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
	// @ fold slayers.PathPoolMem(p.scionLayer.pathPool, p.scionLayer.pathPoolRaw)
	p.scionLayer.RecyclePaths()
	// @ fold p.scionLayer.NonInitMem()
	// @ fold p.initMem()
	return p
}

// @ preserves acc(&p.rawPkt) && acc(&p.path) && acc(&p.hopField) && acc(&p.infoField)
// @ preserves acc(&p.segmentChange) && acc(&p.buffer) && acc(&p.mac) && acc(&p.cachedMac)
// @ preserves p.buffer != nil && p.buffer.Mem()
// @ preserves p.mac != nil && p.mac.Mem()
// @ ensures   p.rawPkt == nil && p.path == nil
// @ ensures   p.hopField == path.HopField{} && p.infoField == path.InfoField{}
// @ ensures   !p.segmentChange
// @ ensures   err != nil ==> err.ErrorMem()
// @ decreases
func (p *scionPacketProcessor) reset() (err error) {
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

// @ requires  p.scionLayer.NonInitMem() && p.hbhLayer.NonInitMem() && p.e2eLayer.NonInitMem()
// @ requires sl.AbsSlice_Bytes(rawPkt, 0, len(rawPkt))
// @ requires acc(&p.rawPkt) && acc(&p.path) && acc(&p.hopField) && acc(&p.infoField)
// @ requires acc(&p.segmentChange) && acc(&p.buffer) && acc(&p.mac) && acc(&p.cachedMac)
// @ requires acc(&p.srcAddr) && acc(&p.lastLayer)
// @ requires p.buffer != nil && p.buffer.Mem()
// @ requires p.mac != nil && p.mac.Mem()
// @ requires acc(srcAddr.Mem(), _)
// @ ensures  reserr != nil ==> reserr.ErrorMem()
// TODO:
//
//	ensure every resource that appears in the precondition
//
// @ decreases
func (p *scionPacketProcessor) processPkt(rawPkt []byte,
	srcAddr *net.UDPAddr) (respr processResult, reserr error) {

	if err := p.reset(); err != nil {
		return processResult{}, err
	}
	p.rawPkt = rawPkt
	p.srcAddr = srcAddr

	// parse SCION header and skip extensions;
	var err error
	// @ ghost var processed seq[bool]
	// @ ghost var offsets   seq[offsetPair]
	// @ ghost var lastLayerIdx int
	p.lastLayer, err /*@ , processed, offsets, lastLayerIdx @*/ = decodeLayers(p.rawPkt, &p.scionLayer, &p.hbhLayer, &p.e2eLayer)
	if err != nil {
		return processResult{}, err
	}
	/*@
	ghost var ub []byte
	ghost if lastLayerIdx == -1 {
		ub = p.rawPkt
	} else {
		if offsets[lastLayerIdx].isNil {
			ub = nil
		} else {
			o := offsets[lastLayerIdx]
			ub = p.rawPkt[o.start:o.end]
		}
	}
	@*/
	pld /*@ , start, end @*/ := p.lastLayer.LayerPayload( /*@ ub @*/ )

	pathType := /*@ unfolding p.scionLayer.Mem(rawPkt) in @*/ p.scionLayer.PathType
	switch pathType {
	case empty.PathType:
		if p.lastLayer.NextLayerType( /*@ ub @*/ ) == layers.LayerTypeBFD {
			// @ def.TODO()
			return processResult{}, p.processIntraBFD(pld)
		}
		// @ establishMemUnsupportedPathTypeNextHeader()
		return processResult{}, serrors.WithCtx(unsupportedPathTypeNextHeader,
			"type", pathType, "header", nextHdr(p.lastLayer /*@, ub @*/))
	case onehop.PathType:
		if p.lastLayer.NextLayerType( /*@ ub @*/ ) == layers.LayerTypeBFD {
			// @ unfold acc(p.scionLayer.Mem(ub), def.ReadL10)
			ohp, ok := p.scionLayer.Path.(*onehop.Path)
			// @ fold acc(p.scionLayer.Mem(ub), def.ReadL10)
			if !ok {
				return processResult{}, malformedPath
			}
			// @ def.TODO()
			return processResult{}, p.processInterBFD(ohp, pld)
		}
		// @ def.TODO()
		return p.processOHP()
	case scion.PathType:
		// @ def.TODO()
		return p.processSCION()
	case epic.PathType:
		// @ def.TODO()
		return p.processEPIC()
	default:
		// @ establishMemUnsupportedPathType()
		return processResult{}, serrors.WithCtx(unsupportedPathType, "type", pathType)
	}
}

// @ trusted
// @ requires false
func (p *scionPacketProcessor) processInterBFD(oh *onehop.Path, data []byte) error {
	if len(p.d.bfdSessions) == 0 {
		return noBFDSessionConfigured
	}

	bfd := &p.bfdLayer
	if err := bfd.DecodeFromBytes(data, gopacket.NilDecodeFeedback); err != nil {
		return err
	}

	if v, ok := p.d.bfdSessions[p.ingressID]; ok {
		v.ReceiveMessage(bfd)
		return nil
	}

	return noBFDSessionFound
}

// @ trusted
// @ requires false
func (p *scionPacketProcessor) processIntraBFD(data []byte) error {
	if len(p.d.bfdSessions) == 0 {
		return noBFDSessionConfigured
	}

	bfd := &p.bfdLayer
	if err := bfd.DecodeFromBytes(data, gopacket.NilDecodeFeedback); err != nil {
		return err
	}

	ifID := uint16(0)
	for k, v := range p.d.internalNextHops {
		if bytes.Equal(v.IP, p.srcAddr.IP) && v.Port == p.srcAddr.Port {
			ifID = k
			break
		}
	}

	if v, ok := p.d.bfdSessions[ifID]; ok {
		v.ReceiveMessage(bfd)
		return nil
	}

	return noBFDSessionFound
}

// @ trusted
// @ requires false
func (p *scionPacketProcessor) processSCION() (processResult, error) {

	var ok bool
	p.path, ok = p.scionLayer.Path.(*scion.Raw)
	if !ok {
		// TODO(lukedirtwalker) parameter problem invalid path?
		return processResult{}, malformedPath
	}
	return p.process()
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

	rawSCMP, err := p.prepareSCMP(typ, code, scmpP, cause)
	return processResult{OutPkt: rawSCMP}, err
}

// @ trusted
// @ requires false
func (p *scionPacketProcessor) parsePath() (processResult, error) {
	var err error
	p.hopField, err = p.path.GetCurrentHopField()
	if err != nil {
		// TODO(lukedirtwalker) parameter problem invalid path?
		return processResult{}, err
	}
	p.infoField, err = p.path.GetCurrentInfoField()
	if err != nil {
		// TODO(lukedirtwalker) parameter problem invalid path?
		return processResult{}, err
	}
	return processResult{}, nil
}

// @ trusted
// @ requires false
func (p *scionPacketProcessor) validateHopExpiry() (processResult, error) {
	expiration := util.SecsToTime(p.infoField.Timestamp).
		Add(path.ExpTimeToDuration(p.hopField.ExpTime))
	expired := expiration.Before(time.Now())
	if !expired {
		return processResult{}, nil
	}
	return p.packSCMP(
		slayers.SCMPTypeParameterProblem,
		slayers.SCMPCodePathExpired,
		&slayers.SCMPParameterProblem{Pointer: p.currentHopPointer()},
		serrors.New("expired hop", "cons_dir", p.infoField.ConsDir, "if_id", p.ingressID,
			"curr_inf", p.path.PathMeta.CurrINF, "curr_hf", p.path.PathMeta.CurrHF),
	)
}

// @ trusted
// @ requires false
func (p *scionPacketProcessor) validateIngressID() (processResult, error) {
	pktIngressID := p.hopField.ConsIngress
	errCode := slayers.SCMPCodeUnknownHopFieldIngress
	if !p.infoField.ConsDir {
		pktIngressID = p.hopField.ConsEgress
		errCode = slayers.SCMPCodeUnknownHopFieldEgress
	}
	if p.ingressID != 0 && p.ingressID != pktIngressID {
		return p.packSCMP(
			slayers.SCMPTypeParameterProblem,
			errCode,
			&slayers.SCMPParameterProblem{Pointer: p.currentHopPointer()},
			serrors.New("ingress interface invalid",
				"pkt_ingress", pktIngressID, "router_ingress", p.ingressID),
		)
	}
	return processResult{}, nil
}

// @ trusted
// @ requires false
func (p *scionPacketProcessor) validateSrcDstIA() (processResult, error) {
	srcIsLocal := (p.scionLayer.SrcIA == p.d.localIA)
	dstIsLocal := (p.scionLayer.DstIA == p.d.localIA)
	if p.ingressID == 0 {
		// Outbound
		// Only check SrcIA if first hop, for transit this already checked by ingress router.
		// Note: SCMP error messages triggered by the sibling router may use paths that
		// don't start with the first hop.
		if p.path.IsFirstHop() && !srcIsLocal {
			return p.invalidSrcIA()
		}
		if dstIsLocal {
			return p.invalidDstIA()
		}
	} else {
		// Inbound
		if srcIsLocal {
			return p.invalidSrcIA()
		}
		if p.path.IsLastHop() != dstIsLocal {
			return p.invalidDstIA()
		}
	}
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
// @ trusted
// @ requires false
func (p *scionPacketProcessor) validateTransitUnderlaySrc() (processResult, error) {
	if p.path.IsFirstHop() || p.ingressID != 0 {
		// not a transit packet, nothing to check
		return processResult{}, nil
	}
	pktIngressID := p.ingressInterface()
	expectedSrc, ok := p.d.internalNextHops[pktIngressID]
	if !ok || !expectedSrc.IP.Equal(p.srcAddr.IP) {
		// Drop
		return processResult{}, invalidSrcAddrForTransit
	}
	return processResult{}, nil
}

// @ trusted
// @ requires false
func (p *scionPacketProcessor) validateEgressID() (processResult, error) {
	pktEgressID := p.egressInterface()
	_, ih := p.d.internalNextHops[pktEgressID]
	_, eh := p.d.external[pktEgressID]
	if !ih && !eh {
		errCode := slayers.SCMPCodeUnknownHopFieldEgress
		if !p.infoField.ConsDir {
			errCode = slayers.SCMPCodeUnknownHopFieldIngress
		}
		return p.packSCMP(
			slayers.SCMPTypeParameterProblem,
			errCode,
			&slayers.SCMPParameterProblem{Pointer: p.currentHopPointer()},
			cannotRoute,
		)
	}

	ingress, egress := p.d.linkTypes[p.ingressID], p.d.linkTypes[pktEgressID]
	if !p.segmentChange {
		// Check that the interface pair is valid within a single segment.
		// No check required if the packet is received from an internal interface.
		switch {
		case p.ingressID == 0:
			return processResult{}, nil
		case ingress == topology.Core && egress == topology.Core:
			return processResult{}, nil
		case ingress == topology.Child && egress == topology.Parent:
			return processResult{}, nil
		case ingress == topology.Parent && egress == topology.Child:
			return processResult{}, nil
		default: // malicious
			return p.packSCMP(
				slayers.SCMPTypeParameterProblem,
				slayers.SCMPCodeInvalidPath, // XXX(matzf) new code InvalidHop?
				&slayers.SCMPParameterProblem{Pointer: p.currentHopPointer()},
				serrors.WithCtx(cannotRoute, "ingress_id", p.ingressID, "ingress_type", ingress,
					"egress_id", pktEgressID, "egress_type", egress))
		}
	}
	// Check that the interface pair is valid on a segment switch.
	// Having a segment change received from the internal interface is never valid.
	switch {
	case ingress == topology.Core && egress == topology.Child:
		return processResult{}, nil
	case ingress == topology.Child && egress == topology.Core:
		return processResult{}, nil
	case ingress == topology.Child && egress == topology.Child:
		return processResult{}, nil
	default:
		return p.packSCMP(
			slayers.SCMPTypeParameterProblem,
			slayers.SCMPCodeInvalidSegmentChange,
			&slayers.SCMPParameterProblem{Pointer: p.currentInfoPointer()},
			serrors.WithCtx(cannotRoute, "ingress_id", p.ingressID, "ingress_type", ingress,
				"egress_id", pktEgressID, "egress_type", egress))
	}
}

// @ trusted
// @ requires false
func (p *scionPacketProcessor) updateNonConsDirIngressSegID() error {
	// against construction dir the ingress router updates the SegID, ifID == 0
	// means this comes from this AS itself, so nothing has to be done.
	// TODO(lukedirtwalker): For packets destined to peer links this shouldn't
	// be updated.
	if !p.infoField.ConsDir && p.ingressID != 0 {
		p.infoField.UpdateSegID(p.hopField.Mac)
		if err := p.path.SetInfoField(p.infoField, int(p.path.PathMeta.CurrINF)); err != nil {
			return serrors.WrapStr("update info field", err)
		}
	}
	return nil
}

// @ trusted
// @ requires false
func (p *scionPacketProcessor) currentInfoPointer() uint16 {
	return uint16(slayers.CmnHdrLen + p.scionLayer.AddrHdrLen() +
		scion.MetaLen + path.InfoLen*int(p.path.PathMeta.CurrINF))
}

// @ trusted
// @ requires false
func (p *scionPacketProcessor) currentHopPointer() uint16 {
	return uint16(slayers.CmnHdrLen + p.scionLayer.AddrHdrLen() +
		scion.MetaLen + path.InfoLen*p.path.NumINF + path.HopLen*int(p.path.PathMeta.CurrHF))
}

// @ trusted
// @ requires false
func (p *scionPacketProcessor) verifyCurrentMAC() (processResult, error) {
	fullMac := path.FullMAC(p.mac, p.infoField, p.hopField, p.macBuffers.scionInput)
	if subtle.ConstantTimeCompare(p.hopField.Mac[:path.MacLen], fullMac[:path.MacLen]) == 0 {
		return p.packSCMP(
			slayers.SCMPTypeParameterProblem,
			slayers.SCMPCodeInvalidHopFieldMAC,
			&slayers.SCMPParameterProblem{Pointer: p.currentHopPointer()},
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

	return processResult{}, nil
}

// @ trusted
// @ requires false
func (p *scionPacketProcessor) resolveInbound() (*net.UDPAddr, processResult, error) {
	a, err := p.d.resolveLocalDst(p.scionLayer)
	switch {
	case errors.Is(err, noSVCBackend):
		r, err := p.packSCMP(
			slayers.SCMPTypeDestinationUnreachable,
			slayers.SCMPCodeNoRoute,
			&slayers.SCMPDestinationUnreachable{}, err)
		return nil, r, err
	default:
		return a, processResult{}, nil
	}
}

// @ trusted
// @ requires false
func (p *scionPacketProcessor) processEgress() error {
	// we are the egress router and if we go in construction direction we
	// need to update the SegID.
	if p.infoField.ConsDir {
		p.infoField.UpdateSegID(p.hopField.Mac)
		if err := p.path.SetInfoField(p.infoField, int(p.path.PathMeta.CurrINF)); err != nil {
			// TODO parameter problem invalid path
			return serrors.WrapStr("update info field", err)
		}
	}
	if err := p.path.IncPath(); err != nil {
		// TODO parameter problem invalid path
		return serrors.WrapStr("incrementing path", err)
	}
	return nil
}

// @ trusted
// @ requires false
func (p *scionPacketProcessor) doXover() (processResult, error) {
	p.segmentChange = true
	if err := p.path.IncPath(); err != nil {
		// TODO parameter problem invalid path
		return processResult{}, serrors.WrapStr("incrementing path", err)
	}
	var err error
	if p.hopField, err = p.path.GetCurrentHopField(); err != nil {
		// TODO parameter problem invalid path
		return processResult{}, err
	}
	if p.infoField, err = p.path.GetCurrentInfoField(); err != nil {
		// TODO parameter problem invalid path
		return processResult{}, err
	}
	return processResult{}, nil
}

// @ trusted
// @ requires false
func (p *scionPacketProcessor) ingressInterface() uint16 {
	info := p.infoField
	hop := p.hopField
	if p.path.IsFirstHopAfterXover() {
		var err error
		info, err = p.path.GetInfoField(int(p.path.PathMeta.CurrINF) - 1)
		if err != nil { // cannot be out of range
			panic(err)
		}
		hop, err = p.path.GetHopField(int(p.path.PathMeta.CurrHF) - 1)
		if err != nil { // cannot be out of range
			panic(err)
		}
	}
	if info.ConsDir {
		return hop.ConsIngress
	}
	return hop.ConsEgress
}

// @ trusted
// @ requires false
func (p *scionPacketProcessor) egressInterface() uint16 {
	if p.infoField.ConsDir {
		return p.hopField.ConsEgress
	}
	return p.hopField.ConsIngress
}

// @ trusted
// @ requires false
func (p *scionPacketProcessor) validateEgressUp() (processResult, error) {
	egressID := p.egressInterface()
	if v, ok := p.d.bfdSessions[egressID]; ok {
		if !v.IsUp() {
			typ := slayers.SCMPTypeExternalInterfaceDown
			var scmpP gopacket.SerializableLayer = &slayers.SCMPExternalInterfaceDown{
				IA:   p.d.localIA,
				IfID: uint64(egressID),
			}
			if _, external := p.d.external[egressID]; !external {
				typ = slayers.SCMPTypeInternalConnectivityDown
				scmpP = &slayers.SCMPInternalConnectivityDown{
					IA:      p.d.localIA,
					Ingress: uint64(p.ingressID),
					Egress:  uint64(egressID),
				}
			}
			return p.packSCMP(typ, 0, scmpP, serrors.New("bfd session down"))
		}
	}
	return processResult{}, nil
}

// @ trusted
// @ requires false
func (p *scionPacketProcessor) handleIngressRouterAlert() (processResult, error) {
	if p.ingressID == 0 {
		return processResult{}, nil
	}
	alert := p.ingressRouterAlertFlag()
	if !*alert {
		return processResult{}, nil
	}
	*alert = false
	if err := p.path.SetHopField(p.hopField, int(p.path.PathMeta.CurrHF)); err != nil {
		return processResult{}, serrors.WrapStr("update hop field", err)
	}
	return p.handleSCMPTraceRouteRequest(p.ingressID)
}

// @ trusted
// @ requires false
func (p *scionPacketProcessor) ingressRouterAlertFlag() *bool {
	if !p.infoField.ConsDir {
		return &p.hopField.EgressRouterAlert
	}
	return &p.hopField.IngressRouterAlert
}

// @ trusted
// @ requires false
func (p *scionPacketProcessor) handleEgressRouterAlert() (processResult, error) {
	alert := p.egressRouterAlertFlag()
	if !*alert {
		return processResult{}, nil
	}
	egressID := p.egressInterface()
	if _, ok := p.d.external[egressID]; !ok {
		return processResult{}, nil
	}
	*alert = false
	if err := p.path.SetHopField(p.hopField, int(p.path.PathMeta.CurrHF)); err != nil {
		return processResult{}, serrors.WrapStr("update hop field", err)
	}
	return p.handleSCMPTraceRouteRequest(egressID)
}

// @ trusted
// @ requires false
func (p *scionPacketProcessor) egressRouterAlertFlag() *bool {
	if !p.infoField.ConsDir {
		return &p.hopField.IngressRouterAlert
	}
	return &p.hopField.EgressRouterAlert
}

// @ trusted
// @ requires false
func (p *scionPacketProcessor) handleSCMPTraceRouteRequest(
	interfaceID uint16) (processResult, error) {

	if p.lastLayer.NextLayerType() != slayers.LayerTypeSCMP {
		log.Debug("Packet with router alert, but not SCMP")
		return processResult{}, nil
	}
	scionPld := p.lastLayer.LayerPayload()
	var scmpH slayers.SCMP
	if err := scmpH.DecodeFromBytes(scionPld, gopacket.NilDecodeFeedback); err != nil {
		log.Debug("Parsing SCMP header of router alert", "err", err)
		return processResult{}, nil
	}
	if scmpH.TypeCode != slayers.CreateSCMPTypeCode(slayers.SCMPTypeTracerouteRequest, 0) {
		log.Debug("Packet with router alert, but not traceroute request",
			"type_code", scmpH.TypeCode)
		return processResult{}, nil
	}
	var scmpP slayers.SCMPTraceroute
	if err := scmpP.DecodeFromBytes(scmpH.Payload, gopacket.NilDecodeFeedback); err != nil {
		log.Debug("Parsing SCMPTraceroute", "err", err)
		return processResult{}, nil
	}
	scmpP = slayers.SCMPTraceroute{
		Identifier: scmpP.Identifier,
		Sequence:   scmpP.Sequence,
		IA:         p.d.localIA,
		Interface:  uint64(interfaceID),
	}
	return p.packSCMP(slayers.SCMPTypeTracerouteReply, 0, &scmpP, nil)
}

// @ trusted
// @ requires false
func (p *scionPacketProcessor) validatePktLen() (processResult, error) {
	if int(p.scionLayer.PayloadLen) == len(p.scionLayer.Payload) {
		return processResult{}, nil
	}
	return p.packSCMP(
		slayers.SCMPTypeParameterProblem,
		slayers.SCMPCodeInvalidPacketSize,
		&slayers.SCMPParameterProblem{Pointer: 0},
		serrors.New("bad packet size",
			"header", p.scionLayer.PayloadLen, "actual", len(p.scionLayer.Payload)),
	)
}

// @ trusted
// @ requires false
func (p *scionPacketProcessor) process() (processResult, error) {

	if r, err := p.parsePath(); err != nil {
		return r, err
	}
	if r, err := p.validateHopExpiry(); err != nil {
		return r, err
	}
	if r, err := p.validateIngressID(); err != nil {
		return r, err
	}
	if r, err := p.validatePktLen(); err != nil {
		return r, err
	}
	if r, err := p.validateTransitUnderlaySrc(); err != nil {
		return r, err
	}
	if r, err := p.validateSrcDstIA(); err != nil {
		return r, err
	}
	if err := p.updateNonConsDirIngressSegID(); err != nil {
		return processResult{}, err
	}
	if r, err := p.verifyCurrentMAC(); err != nil {
		return r, err
	}
	if r, err := p.handleIngressRouterAlert(); err != nil {
		return r, err
	}

	// Inbound: pkts destined to the local IA.
	if p.scionLayer.DstIA == p.d.localIA {
		a, r, err := p.resolveInbound()
		if err != nil {
			return r, err
		}
		return processResult{OutConn: p.d.internal, OutAddr: a, OutPkt: p.rawPkt}, nil
	}

	// Outbound: pkts leaving the local IA.
	// BRTransit: pkts leaving from the same BR different interface.

	if p.path.IsXover() {
		if r, err := p.doXover(); err != nil {
			return r, err
		}
		if r, err := p.validateHopExpiry(); err != nil {
			return r, serrors.WithCtx(err, "info", "after xover")
		}
		// verify the new block
		if r, err := p.verifyCurrentMAC(); err != nil {
			return r, serrors.WithCtx(err, "info", "after xover")
		}
	}
	if r, err := p.validateEgressID(); err != nil {
		return r, err
	}
	// handle egress router alert before we check if it's up because we want to
	// send the reply anyway, so that trace route can pinpoint the exact link
	// that failed.
	if r, err := p.handleEgressRouterAlert(); err != nil {
		return r, err
	}
	if r, err := p.validateEgressUp(); err != nil {
		return r, err
	}

	egressID := p.egressInterface()
	if c, ok := p.d.external[egressID]; ok {
		if err := p.processEgress(); err != nil {
			return processResult{}, err
		}
		return processResult{EgressID: egressID, OutConn: c, OutPkt: p.rawPkt}, nil
	}

	// ASTransit: pkts leaving from another AS BR.
	if a, ok := p.d.internalNextHops[egressID]; ok {
		return processResult{OutConn: p.d.internal, OutAddr: a, OutPkt: p.rawPkt}, nil
	}
	errCode := slayers.SCMPCodeUnknownHopFieldEgress
	if !p.infoField.ConsDir {
		errCode = slayers.SCMPCodeUnknownHopFieldIngress
	}
	return p.packSCMP(
		slayers.SCMPTypeParameterProblem,
		errCode,
		&slayers.SCMPParameterProblem{Pointer: p.currentHopPointer()},
		cannotRoute,
	)
}

// @ trusted
// @ requires false
func (p *scionPacketProcessor) processOHP() (processResult, error) {
	s := p.scionLayer
	ohp, ok := s.Path.(*onehop.Path)
	if !ok {
		// TODO parameter problem -> invalid path
		return processResult{}, malformedPath
	}
	if !ohp.Info.ConsDir {
		// TODO parameter problem -> invalid path
		return processResult{}, serrors.WrapStr(
			"OneHop path in reverse construction direction is not allowed",
			malformedPath, "srcIA", s.SrcIA, "dstIA", s.DstIA)
	}

	// OHP leaving our IA
	if p.ingressID == 0 {
		if !p.d.localIA.Equal(s.SrcIA) {
			// TODO parameter problem -> invalid path
			return processResult{}, serrors.WrapStr("bad source IA", cannotRoute,
				"type", "ohp", "egress", ohp.FirstHop.ConsEgress,
				"localIA", p.d.localIA, "srcIA", s.SrcIA)
		}
		neighborIA, ok := p.d.neighborIAs[ohp.FirstHop.ConsEgress]
		if !ok {
			// TODO parameter problem invalid interface
			return processResult{}, serrors.WithCtx(cannotRoute,
				"type", "ohp", "egress", ohp.FirstHop.ConsEgress)
		}
		if !neighborIA.Equal(s.DstIA) {
			return processResult{}, serrors.WrapStr("bad destination IA", cannotRoute,
				"type", "ohp", "egress", ohp.FirstHop.ConsEgress,
				"neighborIA", neighborIA, "dstIA", s.DstIA)
		}
		mac := path.MAC(p.mac, ohp.Info, ohp.FirstHop, p.macBuffers.scionInput)
		if subtle.ConstantTimeCompare(ohp.FirstHop.Mac[:], mac[:]) == 0 {
			// TODO parameter problem -> invalid MAC
			return processResult{}, serrors.New("MAC", "expected", fmt.Sprintf("%x", mac),
				"actual", fmt.Sprintf("%x", ohp.FirstHop.Mac), "type", "ohp")
		}
		ohp.Info.UpdateSegID(ohp.FirstHop.Mac)

		if err := updateSCIONLayer(p.rawPkt, s, p.buffer); err != nil {
			return processResult{}, err
		}
		// OHP should always be directed to the correct BR.
		if c, ok := p.d.external[ohp.FirstHop.ConsEgress]; ok {
			// buffer should already be correct
			return processResult{EgressID: ohp.FirstHop.ConsEgress, OutConn: c, OutPkt: p.rawPkt},
				nil
		}
		// TODO parameter problem invalid interface
		return processResult{}, serrors.WithCtx(cannotRoute, "type", "ohp",
			"egress", ohp.FirstHop.ConsEgress, "consDir", ohp.Info.ConsDir)
	}

	// OHP entering our IA
	if !p.d.localIA.Equal(s.DstIA) {
		return processResult{}, serrors.WrapStr("bad destination IA", cannotRoute,
			"type", "ohp", "ingress", p.ingressID,
			"localIA", p.d.localIA, "dstIA", s.DstIA)
	}
	neighborIA := p.d.neighborIAs[p.ingressID]
	if !neighborIA.Equal(s.SrcIA) {
		return processResult{}, serrors.WrapStr("bad source IA", cannotRoute,
			"type", "ohp", "ingress", p.ingressID,
			"neighborIA", neighborIA, "srcIA", s.SrcIA)
	}

	ohp.SecondHop = path.HopField{
		ConsIngress: p.ingressID,
		ExpTime:     ohp.FirstHop.ExpTime,
	}
	// XXX(roosd): Here we leak the buffer into the SCION packet header.
	// This is okay because we do not operate on the buffer or the packet
	// for the rest of processing.
	ohp.SecondHop.Mac = path.MAC(p.mac, ohp.Info, ohp.SecondHop, p.macBuffers.scionInput)

	if err := updateSCIONLayer(p.rawPkt, s, p.buffer); err != nil {
		return processResult{}, err
	}
	a, err := p.d.resolveLocalDst(s)
	if err != nil {
		return processResult{}, err
	}
	return processResult{OutConn: p.d.internal, OutAddr: a, OutPkt: p.rawPkt}, nil
}

// @ trusted
// @ requires false
func (d *DataPlane) resolveLocalDst(s slayers.SCION) (*net.UDPAddr, error) {
	dst, err := s.DstAddr()
	if err != nil {
		// TODO parameter problem.
		return nil, err
	}
	switch v := dst.(type) {
	case addr.HostSVC:
		// For map lookup use the Base address, i.e. strip the multi cast
		// information, because we only register base addresses in the map.
		a, ok := d.svc.Any(v.Base())
		if !ok {
			return nil, noSVCBackend
		}
		return a, nil
	case *net.IPAddr:
		return addEndhostPort(v), nil
	default:
		panic("unexpected address type returned from DstAddr")
	}
}

// @ trusted
// @ requires false
func addEndhostPort(dst *net.IPAddr) *net.UDPAddr {
	return &net.UDPAddr{IP: dst.IP, Port: topology.EndhostPort}
}

// TODO(matzf) this function is now only used to update the OneHop-path.
// This should be changed so that the OneHop-path can be updated in-place, like
// the scion.Raw path.
// @ trusted
// @ requires false
func updateSCIONLayer(rawPkt []byte, s slayers.SCION, buffer gopacket.SerializeBuffer) error {
	if err := buffer.Clear(); err != nil {
		return err
	}
	if err := s.SerializeTo(buffer, gopacket.SerializeOptions{}); err != nil {
		return err
	}
	// TODO(lukedirtwalker): We should add a method to the scion layers
	// which can write into the existing buffer, see also the discussion in
	// https://fsnets.slack.com/archives/C8ADBBG0J/p1592805884250700
	rawContents := buffer.Bytes()
	copy(rawPkt[:len(rawContents)], rawContents)
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

// @ preserves acc(b.Mem(), def.ReadL10)
// @ decreases
func (b *bfdSend) String() string {
	// @ unfold acc(b.Mem(), def.ReadL10)
	// @ ghost defer fold acc(b.Mem(), def.ReadL10)
	return b.srcAddr.String()
}

// Send sends out a BFD message.
// Due to the internal state of the MAC computation, this is not goroutine
// safe.
// @ trusted
// @ requires def.Uncallable()
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

// @ trusted
// @ requires false
func (p *scionPacketProcessor) prepareSCMP(
	typ slayers.SCMPType,
	code slayers.SCMPCode,
	scmpP gopacket.SerializableLayer,
	cause error,
) ([]byte, error) {

	// *copy* and reverse path -- the original path should not be modified as this writes directly
	// back to rawPkt (quote).
	var path *scion.Raw
	pathType := p.scionLayer.Path.Type()
	switch pathType {
	case scion.PathType:
		var ok bool
		path, ok = p.scionLayer.Path.(*scion.Raw)
		if !ok {
			return nil, serrors.WithCtx(cannotRoute, "details", "unsupported path type",
				"path type", pathType)
		}
	case epic.PathType:
		epicPath, ok := p.scionLayer.Path.(*epic.Path)
		if !ok {
			return nil, serrors.WithCtx(cannotRoute, "details", "unsupported path type",
				"path type", pathType)
		}
		path = epicPath.ScionPath
	default:
		return nil, serrors.WithCtx(cannotRoute, "details", "unsupported path type",
			"path type", pathType)
	}
	decPath, err := path.ToDecoded()
	if err != nil {
		return nil, serrors.Wrap(cannotRoute, err, "details", "decoding raw path")
	}
	revPathTmp, err := decPath.Reverse()
	if err != nil {
		return nil, serrors.Wrap(cannotRoute, err, "details", "reversing path for SCMP")
	}
	revPath := revPathTmp.(*scion.Decoded)

	// Revert potential path segment switches that were done during processing.
	if revPath.IsXover() {
		if err := revPath.IncPath(); err != nil {
			return nil, serrors.Wrap(cannotRoute, err, "details", "reverting cross over for SCMP")
		}
	}
	// If the packet is sent to an external router, we need to increment the
	// path to prepare it for the next hop.
	_, external := p.d.external[p.ingressID]
	if external {
		infoField := &revPath.InfoFields[revPath.PathMeta.CurrINF]
		if infoField.ConsDir {
			hopField := revPath.HopFields[revPath.PathMeta.CurrHF]
			infoField.UpdateSegID(hopField.Mac)
		}
		if err := revPath.IncPath(); err != nil {
			return nil, serrors.Wrap(cannotRoute, err, "details", "incrementing path for SCMP")
		}
	}

	// create new SCION header for reply.
	var scionL slayers.SCION
	scionL.FlowID = p.scionLayer.FlowID
	scionL.TrafficClass = p.scionLayer.TrafficClass
	scionL.PathType = revPath.Type()
	scionL.Path = revPath
	scionL.DstIA = p.scionLayer.SrcIA
	scionL.SrcIA = p.d.localIA
	srcA, err := p.scionLayer.SrcAddr()
	if err != nil {
		return nil, serrors.Wrap(cannotRoute, err, "details", "extracting src addr")
	}
	if err := scionL.SetDstAddr(srcA); err != nil {
		return nil, serrors.Wrap(cannotRoute, err, "details", "setting dest addr")
	}
	if err := scionL.SetSrcAddr(&net.IPAddr{IP: p.d.internalIP}); err != nil {
		return nil, serrors.Wrap(cannotRoute, err, "details", "setting src addr")
	}
	scionL.NextHdr = slayers.L4SCMP

	typeCode := slayers.CreateSCMPTypeCode(typ, code)
	scmpH := slayers.SCMP{TypeCode: typeCode}
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
		hdrLen := slayers.CmnHdrLen + scionL.AddrHdrLen() + scionL.Path.Len()
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
		scmpLayers = append(scmpLayers, gopacket.Payload(quote))
	}
	// XXX(matzf) could we use iovec gather to avoid copying quote?
	err = gopacket.SerializeLayers(p.buffer, sopts, scmpLayers...)
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
// @     (acc(&opts[i], def.ReadL10) && opts[i] != nil && opts[i].NonInitMem())
// Due to Viper's very strict injectivity constraints:
// @ requires  forall i, j int :: { &opts[i], &opts[j] } 0 <= i && i < j && j < len(opts) ==>
// @     opts[i] !== opts[j]
// @ preserves slices.AbsSlice_Bytes(data, 0, len(data))
// @ ensures   forall i int :: { &opts[i] } 0 <= i && i < len(opts) ==>
// @     (acc(&opts[i], def.ReadL10) && opts[i] != nil)
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

	// @ invariant slices.AbsSlice_Bytes(oldData, 0, len(oldData))
	// @ invariant base.Mem(oldData)
	// @ invariant 0 < len(opts) ==> 0 <= i0 && i0 <= len(opts)
	// @ invariant forall i int :: {&opts[i]} 0 <= i && i < len(opts) ==> acc(&opts[i], def.ReadL10)
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
			// @ 	slices.NilAcc_Bytes()
			// @ } else {
			// @	slices.SplitRange_Bytes(oldData, oldStart, oldEnd, writePerm)
			// @ }
			if err := opt.DecodeFromBytes(data, gopacket.NilDecodeFeedback); err != nil {
				// @ ghost if data != nil { slices.CombineRange_Bytes(oldData, oldStart, oldEnd, writePerm) }
				// @ base.DowngradePerm(oldData)

				// ghost clean-up:
				// @ ghost
				// @ invariant 0 <= i0 && i0 <= len(opts)
				// @ invariant -1 <= c && c <= i0
				// @ invariant len(processed) == len(opts)
				// @ invariant len(offsets) == len(opts)
				// @ invariant forall i int :: {&opts[i]} 0 <= i && i < len(opts) ==> acc(&opts[i], def.ReadL10)
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
			// @ ghost if data != nil { slices.CombineRange_Bytes(oldData, oldStart, oldEnd, writePerm) }
			last = opt
		}
	}
	return last, nil /*@ , processed, offsets, idx @*/
}

// @ preserves acc(layer.Mem(ubuf), def.ReadL20)
// @ decreases
func nextHdr(layer gopacket.DecodingLayer /*@ , ghost ubuf []byte @*/) slayers.L4ProtocolType {
	switch v := layer.(type) {
	case *slayers.SCION:
		return /*@ unfolding acc(v.Mem(ubuf), def.ReadL20) in @*/ v.NextHdr
	case *slayers.EndToEndExtnSkipper:
		return /*@ unfolding acc(v.Mem(ubuf), def.ReadL20) in (unfolding acc(v.extnBase.Mem(ubuf), def.ReadL20) in @*/ v.NextHdr /*@ ) @*/
	case *slayers.HopByHopExtnSkipper:
		return /*@ unfolding acc(v.Mem(ubuf), def.ReadL20) in (unfolding acc(v.extnBase.Mem(ubuf), def.ReadL20) in @*/ v.NextHdr /*@ ) @*/
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

// @ preserves neighbors != nil ==> acc(neighbors, def.ReadL20)
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
