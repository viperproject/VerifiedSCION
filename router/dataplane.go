// Copyright 2020 Anapaya Systems
// Copyright 2023 ETH Zurich
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
	"context"
	"crypto/rand"
	"crypto/subtle"
	"encoding/binary"
	"errors"
	"fmt"
	"hash"
	"math/big"
	"net"
	"net/netip"
	"sync"
	"sync/atomic"
	"time"
	"unsafe"

	"github.com/google/gopacket"
	"github.com/google/gopacket/layers"
	"github.com/prometheus/client_golang/prometheus"

	"github.com/scionproto/scion/pkg/addr"
	"github.com/scionproto/scion/pkg/drkey"
	libepic "github.com/scionproto/scion/pkg/experimental/epic"
	"github.com/scionproto/scion/pkg/log"
	"github.com/scionproto/scion/pkg/private/processmetrics"
	"github.com/scionproto/scion/pkg/private/serrors"
	"github.com/scionproto/scion/pkg/private/util"
	"github.com/scionproto/scion/pkg/scrypto"

	"github.com/scionproto/scion/pkg/slayers"
	"github.com/scionproto/scion/pkg/slayers/path"
	"github.com/scionproto/scion/pkg/slayers/path/empty"
	"github.com/scionproto/scion/pkg/slayers/path/epic"
	"github.com/scionproto/scion/pkg/slayers/path/onehop"
	"github.com/scionproto/scion/pkg/slayers/path/scion"
	"github.com/scionproto/scion/pkg/spao"
	"github.com/scionproto/scion/private/drkey/drkeyutil"
	"github.com/scionproto/scion/private/topology"
	underlayconn "github.com/scionproto/scion/private/underlay/conn"
	"github.com/scionproto/scion/router/bfd"
	"github.com/scionproto/scion/router/control"
	// @ . "github.com/scionproto/scion/verification/utils/definitions"
	// @ fl "github.com/scionproto/scion/verification/utils/floats"
	// @ gsync "github.com/scionproto/scion/verification/utils/ghost_sync"
	// @ sl "github.com/scionproto/scion/verification/utils/slices"
	// @ "github.com/scionproto/scion/verification/utils/seqs"
	// @ socketspec "golang.org/x/net/internal/socket/"
	// @ io "verification/io"
)

const (
	// TODO(karampok). Investigate whether that value should be higher.  In
	// theory, PayloadLen in SCION header is 16 bits long, supporting a maximum
	// payload size of 64KB. At the moment we are limited by Ethernet size
	// usually ~1500B, but 9000B to support jumbo frames.
	bufSize = 9000

	// hopFieldDefaultExpTime is the default validity of the hop field
	// and 63 is equivalent to 6h.
	hopFieldDefaultExpTime = 63

	// e2eAuthHdrLen is the length in bytes of added information when a SCMP packet
	// needs to be authenticated: 16B (e2e.option.Len()) + 16B (CMAC_tag.Len()).
	e2eAuthHdrLen = 32

	// Needed to compute required padding
	ptrSize = unsafe.Sizeof(&struct{ int }{})
	is32bit = 1 - (ptrSize-4)/4
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
	// @ preserves sl.Bytes(ub, 0, len(ub))
	// @ ensures   msg.NonInitMem()
	// @ decreases 0 if sync.IgnoreBlockingForTermination()
	ReceiveMessage(msg *layers.BFD /*@ , ghost ub []byte @*/)
	// @ requires acc(Mem(), _)
	// @ decreases 0 if sync.IgnoreBlockingForTermination()
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
	// @ requires forall j int :: { &msgs[j] } 0 <= j && j < len(msgs) ==>
	// @ 	sl.Bytes(msgs[j].GetFstBuffer(), 0, len(msgs[j].GetFstBuffer()))
	// @ ensures   forall i int :: { &msgs[i] } 0 <= i && i < len(msgs) ==>
	// @ 	(msgs[i].Mem() && msgs[i].HasActiveAddr())
	// @ ensures   err == nil ==> 0 <= n && n <= len(msgs)
	// @ ensures   err == nil ==>
	// @ 	forall i int :: { &msgs[i] } 0 <= i && i < n ==> (
	// @ 		typeOf(msgs[i].GetAddr()) == type[*net.UDPAddr] &&
	// @ 		!msgs[i].HasWildcardPermAddr())
	// @ ensures   err == nil ==>
	// @ 	forall i int :: { &msgs[i] } 0 <= i && i < n ==> msgs[i].GetN() <= len(msgs[i].GetFstBuffer())
	// @ ensures forall j int :: { &msgs[j] } 0 <= j && j < len(msgs) ==>
	// @ 	sl.Bytes(msgs[j].GetFstBuffer(), 0, len(msgs[j].GetFstBuffer()))
	// @ ensures   err != nil ==> err.ErrorMem()
	// contracts for IO-spec
	// @ requires  Prophecy(prophecyM)
	// @ requires  io.token(place) && MultiReadBio(place, prophecyM)
	// @ ensures   err != nil ==> prophecyM == 0
	// @ ensures   err == nil ==> prophecyM == n
	// @ ensures   io.token(old(MultiReadBioNext(place, prophecyM)))
	// @ ensures   old(MultiReadBioCorrectIfs(place, prophecyM, path.ifsToIO_ifs(ingressID)))
	// @ ensures   err == nil ==>
	// @ 	forall i int :: { &msgs[i] } 0 <= i && i < n ==>
	// @ 		MsgToAbsVal(&msgs[i], ingressID) == old(MultiReadBioIO_val(place, n)[i])
	ReadBatch(msgs underlayconn.Messages /*@, ghost ingressID uint16, ghost prophecyM int, ghost place io.Place @*/) (n int, err error)
	// @ requires  acc(addr.Mem(), _)
	// @ requires  acc(Mem(), _)
	// @ preserves acc(sl.Bytes(b, 0, len(b)), R10)
	// @ ensures   err == nil ==> 0 <= n && n <= len(b)
	// @ ensures   err != nil ==> err.ErrorMem()
	WriteTo(b []byte, addr netip.AddrPort) (n int, err error)
	// @ requires  acc(Mem(), _)
	// (VerifiedSCION) opted for less reusable spec for WriteBatch for
	// performance reasons.
	// @ requires  len(msgs) == 1
	// @ requires  acc(msgs[0].Mem(), R50) && msgs[0].HasActiveAddr()
	// @ requires  acc(sl.Bytes(msgs[0].GetFstBuffer(), 0, len(msgs[0].GetFstBuffer())), R50)
	// preconditions for IO-spec:
	// @ requires  MsgToAbsVal(&msgs[0], egressID) == ioAbsPkts
	// @ requires  io.token(place) && io.CBioIO_bio3s_send(place, ioAbsPkts)
	// @ ensures   acc(msgs[0].Mem(), R50) && msgs[0].HasActiveAddr()
	// @ ensures   acc(sl.Bytes(msgs[0].GetFstBuffer(), 0, len(msgs[0].GetFstBuffer())), R50)
	// @ ensures   err == nil ==> 0 <= n && n <= len(msgs)
	// @ ensures   err != nil ==> err.ErrorMem()
	// postconditions for IO-spec:
	// (VerifiedSCION) the permission to the protocol must always be returned,
	// otherwise the router cannot continue after failing to send a packet.
	// @ ensures   io.token(old(io.dp3s_iospec_bio3s_send_T(place, ioAbsPkts)))
	WriteBatch(msgs underlayconn.Messages, flags int /*@, ghost egressID uint16, ghost place io.Place, ghost ioAbsPkts io.IO_val @*/) (n int, err error)
	// @ requires Mem()
	// @ ensures  err != nil ==> err.ErrorMem()
	// @ decreases
	Close() (err error)
}

type disposition int

const (
	pDiscard disposition = iota // Zero value, default.
	pForward
	pSlowPath
	pDone
)

// packet aggregates buffers and ancillary metadata related to one packet.
// That is everything we need to pass-around while processing a packet. The motivation is to save on
// copy (pass everything via one reference) AND garbage collection (reuse everything).
// The buffer is allocated in a separate location (but still reused) to keep the packet structures
// tightly packed (might not matter, though).
// Golang gives precious little guarantees about alignment and padding. We do it ourselves in such
// a way that Go has no sane reason to add any padding. Everything is 8 byte aligned (on 64 bit
// arch) until Slowpath request which is 6 bytes long. The rest is in decreasing order of size and
// size-aligned. We want to fit neatly into cache lines, so we need to fit in 64 bytes. The padding
// required to occupy exactly 64 bytes depends on the architecture.
type packet struct {
	// The useful part of the raw packet at a point in time (i.e. a slice of the full buffer).
	// TODO(jiceatscion): would it be beneficial to store the length instead, like readBatch does?
	rawPacket []byte
	// The source address. Will be set by the receiver from smsg.Addr. We could update it in-place,
	// but the IP address bytes in it are allocated by readbatch, so if we copy into a recyclable
	// location, it's the original we throw away. No gain (may be a tiny bit?).
	srcAddr *net.UDPAddr
	// The address to where we are forwarding the packet.
	// Will be set by the processing routine; it is updated in-place.
	dstAddr *net.UDPAddr
	// Additional metadata in case the packet is put on the slow path. Updated in-place.
	slowPathRequest slowPathRequest
	// The ingress on which this packet arrived. This is set by the receiver.
	ingress uint16
	// The egress on which this packet must leave. This is set by the processing routine.
	egress uint16
	// The type of traffic. This is used for metrics at the forwarding stage, but is most
	// economically determined at the processing stage. So store it here. It's 2 bytes long.
	trafficType trafficType
	// Pad to 64 bytes. For 64bit arch, add 12 bytes. For 32bit arch, add 32 bytes.
	// TODO(jiceatscion): see if packing two packets per cache line instead is good or bad for 32bit
	// machines.
	_ [12 + is32bit*20]byte
}

// Keep this 6 bytes long. See comment for packet.
type slowPathRequest struct {
	pointer  uint16
	typ      slowPathType
	scmpType slayers.SCMPType
	code     slayers.SCMPCode
	_        uint8
}

// Make sure that the packet structure has the size we expect.
const _ uintptr = 64 - unsafe.Sizeof(packet{}) // assert 64 >= sizeof(packet)
const _ uintptr = unsafe.Sizeof(packet{}) - 64 // assert sizeof(packet) >= 64

// initPacket configures the given blank packet (and returns it, for convenience).
func (p *packet) init(buffer *[bufSize]byte) *packet {
	p.rawPacket = buffer[:]
	p.dstAddr = &net.UDPAddr{IP: make(net.IP, net.IPv6len)}
	return p
}

// reset() makes the packet ready to receive a new underlay message.
// A cleared dstAddr is represented with a zero-length IP so we keep reusing the IP storage bytes.
func (p *packet) reset() {
	p.dstAddr.IP = p.dstAddr.IP[0:0] // We're keeping the object, just blank it.
	*p = packet{
		rawPacket: p.rawPacket[:cap(p.rawPacket)], // keep the slice and so the backing array.
		dstAddr:   p.dstAddr,                      // keep the dstAddr and so the IP slice and bytes
	}
	// Everything else is reset to zero value.

}

// DataPlane contains a SCION Border Router's forwarding logic. It reads packets
// from multiple sockets, performs routing, and sends them to their destinations
// (after updating the path, if that is needed).
type DataPlane struct {
	// (VerifiedSCION) This is stored in the dataplane in order to retain
	// knowledge that macFactory will not fail.
	// @ ghost key *[]byte

	interfaces          map[uint16]BatchConn
	external            map[uint16]BatchConn
	linkTypes           map[uint16]topology.LinkType
	neighborIAs         map[uint16]addr.IA
	peerInterfaces      map[uint16]uint16
	internal            BatchConn
	internalIP          netip.Addr
	internalNextHops    map[uint16]netip.AddrPort
	svc                 *services
	macFactory          func() hash.Hash
	bfdSessions         map[uint16]bfdSession
	localIA             addr.IA
	mtx                 sync.Mutex
	running             atomic.Bool
	Metrics             *Metrics
	forwardingMetrics   map[uint16]interfaceMetrics
	dispatchedPortStart uint16
	dispatchedPortEnd   uint16

	ExperimentalSCMPAuthentication bool

	// The pool that stores all the packet buffers as described in the design document. See
	// https://github.com/scionproto/scion/blob/master/doc/dev/design/BorderRouter.rst
	// To avoid garbage collection, most the meta-data that is produced during the processing of a
	// packet is kept in a data structure (packet struct) that is pooled and recycled along with
	// corresponding packet buffer. The packet struct refers permanently to the packet buffer. The
	// packet structure is fetched from the pool passed-around through the various channels and
	// returned to the pool. To reduce the cost of copying, the packet structure is passed by
	// reference.
	packetPool chan *packet
}

var (
	alreadySet                    = errors.New("already set")
	invalidSrcIA                  = errors.New("invalid source ISD-AS")
	invalidDstIA                  = errors.New("invalid destination ISD-AS")
	invalidSrcAddrForTransit      = errors.New("invalid source address for transit pkt")
	invalidDstAddr                = errors.New("invalid destination address")
	cannotRoute                   = errors.New("cannot route, dropping pkt")
	emptyValue                    = errors.New("empty value")
	malformedPath                 = errors.New("malformed path content")
	modifyExisting                = errors.New("modifying a running dataplane is not allowed")
	noSVCBackend                  = errors.New("cannot find internal IP for the SVC")
	unsupportedPathType           = errors.New("unsupported path type")
	unsupportedPathTypeNextHeader = errors.New("unsupported combination")
	unsupportedV4MappedV6Address  = errors.New("unsupported v4mapped IP v6 address")
	unsupportedUnspecifiedAddress = errors.New("unsupported unspecified address")
	noBFDSessionFound             = errors.New("no BFD session was found")
	noBFDSessionConfigured        = errors.New("no BFD sessions have been configured")
	errPeeringEmptySeg0           = errors.New("zero-length segment[0] in peering path")
	errPeeringEmptySeg1           = errors.New("zero-length segment[1] in peering path")
	errPeeringNonemptySeg2        = errors.New("non-zero-length segment[2] in peering path")
	errShortPacket                = errors.New("Packet is too short")
	errBFDSessionDown             = errors.New("bfd session down")
	expiredHop                    = errors.New("expired hop")
	ingressInterfaceInvalid       = errors.New("ingress interface invalid")
	macVerificationFailed         = errors.New("MAC verification failed")
	badPacketSize                 = errors.New("bad packet size")

	// zeroBuffer will be used to reset the Authenticator option in the
	// scionPacketProcessor.OptAuth
	zeroBuffer = make([]byte, 16)
)

type drkeyProvider interface {
	GetASHostKey(validTime time.Time, dstIA addr.IA, dstAddr addr.Host) (drkey.ASHostKey, error)
	GetKeyWithinAcceptanceWindow(
		validTime time.Time,
		timestamp uint64,
		dstIA addr.IA,
		dstAddr addr.Host,
	) (drkey.ASHostKey, error)
}

// setRunning() Configures the running state of the data plane to true. setRunning() is called once
// the dataplane is finished initializing and is ready to process packets.
func (d *DataPlane) setRunning() {
	d.running.Store(true)
}

// setStopping() Configures the running state of the data plane to false. This should not be called
// during the dataplane initialization. Calling this before initialization starts has no effect.
func (d *DataPlane) setStopping() {
	d.running.Store(false)
}

// IsRunning() Indicates the running state of the data plane. If true, the dataplane is initialized
// and ready to process or already processing packets. In this case some configuration changes are
// not permitted. If false, the data plane is not ready to process packets yet, or is shutting
// down.
func (d *DataPlane) IsRunning() bool {
	return d.running.Load()
}

// Shutdown() causes the dataplane to stop accepting packets and then terminate. Note that
// in that case the router is committed to shutting down. There is no mechanism to restart it.
func (d *DataPlane) Shutdown() {
	d.mtx.Lock() // make sure we're nor racing with initialization.
	defer d.mtx.Unlock()
	d.setStopping()
}

// SetIA sets the local IA for the dataplane.
// @ requires  acc(d.Mem(), OutMutexPerm)
// @ requires  !d.IsRunning()
// @ requires  d.LocalIA().IsZero()
// @ requires  !ia.IsZero()
// @ preserves d.mtx.LockP()
// @ preserves d.mtx.LockInv() == MutexInvariant!<d!>
// @ ensures   acc(d.Mem(), OutMutexPerm)
// @ ensures   !d.IsRunning()
// @ ensures   e == nil
// @ decreases 0 if sync.IgnoreBlockingForTermination()
func (d *DataPlane) SetIA(ia addr.IA) (e error) {
	d.mtx.Lock()
	defer d.mtx.Unlock()
	// @ unfold MutexInvariant!<d!>()
	// @ assert !d.IsRunning()
	// @ d.isRunningEq()
	// @ unfold d.Mem()
	// @ defer fold MutexInvariant!<d!>()
	// @ defer fold d.Mem()
	if d.IsRunning() {
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
// @ requires  sl.Bytes(key, 0, len(key))
// @ preserves d.mtx.LockP()
// @ preserves d.mtx.LockInv() == MutexInvariant!<d!>
// @ ensures   acc(d.Mem(), OutMutexPerm)
// @ ensures   !d.IsRunning()
// @ ensures   res == nil ==> d.KeyIsSet()
// @ decreases 0 if sync.IgnoreBlockingForTermination()
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
	if d.IsRunning() {
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
		// @ requires acc(&key, _) && acc(sl.Bytes(key, 0, len(key)), _)
		// @ requires scrypto.ValidKeyForHash(key)
		// @ ensures  acc(&key, _) && acc(sl.Bytes(key, 0, len(key)), _)
		// @ ensures  h != nil && h.Mem()
		// @ decreases
		func /*@ f @*/ () (h hash.Hash) {
			mac, _ := scrypto.InitMac(key)
			return mac
		}
	// @ proof verScionTemp implements MacFactorySpec{d.key} {
	// @   return verScionTemp() as f
	// @ }
	d.macFactory = verScionTemp
	return nil
}

func (d *DataPlane) SetPortRange(start, end uint16) {
	d.dispatchedPortStart = start
	d.dispatchedPortEnd = end
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
// @ preserves d.mtx.LockInv() == MutexInvariant!<d!>
// @ ensures   acc(d.Mem(), OutMutexPerm)
// @ ensures   !d.IsRunning()
// @ decreases 0 if sync.IgnoreBlockingForTermination()
func (d *DataPlane) AddInternalInterface(conn BatchConn, ip netip.Addr) error {
	d.mtx.Lock()
	defer d.mtx.Unlock()
	// @ unfold MutexInvariant!<d!>()
	// @ assert !d.IsRunning()
	// @ d.isRunningEq()
	// @ unfold acc(d.Mem(), 1/2)
	// @ d.internalIsSetEq()
	// @ unfold acc(d.Mem(), 1/2)
	if d.IsRunning() {
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
	if d.interfaces == nil {
		d.interfaces = make(map[uint16]BatchConn)
	}
	d.interfaces[0] = conn
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
// @ preserves d.mtx.LockInv() == MutexInvariant!<d!>
// @ decreases 0 if sync.IgnoreBlockingForTermination()
func (d *DataPlane) AddExternalInterface(ifID uint16, conn BatchConn,
	src, dst control.LinkEnd, cfg control.BFD) error {

	d.mtx.Lock()
	defer d.mtx.Unlock()
	// @ unfold MutexInvariant!<d!>()
	// @ assert !d.IsRunning()
	// @ d.isRunningEq()
	// @ unfold d.Mem()
	if d.IsRunning() {
		// @ Unreachable()
		return modifyExisting
	}
	if conn == nil || !src.Addr.IsValid() || !dst.Addr.IsValid() {
		// @ Unreachable()
		return emptyValue
	}
	err := d.addExternalInterfaceBFD(ifID, conn, src, dst, cfg)
	if err != nil {
		return serrors.Wrap("adding external BFD", err, "if_id", ifID)
	}
	// @ ghost if d.external != nil { fold acc(accBatchConn(d.external), 1/2) }
	if d.external == nil {
		d.external = make(map[uint16]BatchConn)
		// @ fold accBatchConn(d.external)
	}
	if d.interfaces == nil {
		d.interfaces = make(map[uint16]BatchConn)
	}
	if _, exists := d.external[ifID]; exists {
		return serrors.JoinNoStack(alreadySet, nil, "ifID", ifID)
	}
	d.interfaces[ifID] = conn
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
// @ preserves d.mtx.LockInv() == MutexInvariant!<d!>
// @ decreases 0 if sync.IgnoreBlockingForTermination()
func (d *DataPlane) AddNeighborIA(ifID uint16, remote addr.IA) error {
	d.mtx.Lock()
	defer d.mtx.Unlock()
	// @ unfold MutexInvariant!<d!>()
	// @ d.isRunningEq()
	// @ unfold d.Mem()
	if d.IsRunning() {
		// @ Unreachable()
		return modifyExisting
	}
	if remote.IsZero() {
		// @ Unreachable()
		return emptyValue
	}
	if _, exists := d.neighborIAs[ifID]; exists {
		// @ establishAlreadySet()
		// @ fold d.Mem()
		// @ fold MutexInvariant!<d!>()
		return serrors.JoinNoStack(alreadySet, nil, "ifID", ifID)
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
// @ decreases 0 if sync.IgnoreBlockingForTermination()
func (d *DataPlane) AddLinkType(ifID uint16, linkTo topology.LinkType) error {
	d.mtx.Lock()
	defer d.mtx.Unlock()
	// @ unfold acc(d.Mem(), OutMutexPerm)
	if d.IsRunning() {
		return modifyExisting
	}
	if _, exists := d.linkTypes[ifID]; exists {
		// @ establishAlreadySet()
		// @ fold acc(d.Mem(), OutMutexPerm)
		return serrors.JoinNoStack(alreadySet, nil, "ifID", ifID)
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

// AddRemotePeer adds the remote peering interface ID for local
// interface ID.  If the link type for the given ID is already set to
// a different type, this method will return an error. This can only
// be called on a not yet running dataplane.
func (d *DataPlane) AddRemotePeer(local, remote uint16) error {
	if t, ok := d.linkTypes[local]; ok && t != topology.Peer {
		return serrors.JoinNoStack(unsupportedPathType, nil, "type", t)
	}
	if _, exists := d.peerInterfaces[local]; exists {
		return serrors.JoinNoStack(alreadySet, nil, "local_interface", local)
	}
	if d.peerInterfaces == nil {
		d.peerInterfaces = make(map[uint16]uint16)
	}
	d.peerInterfaces[local] = remote
	return nil
}

// AddExternalInterfaceBFD adds the inter AS connection BFD session.
// @ trusted
// @ requires false
func (d *DataPlane) addExternalInterfaceBFD(ifID uint16, conn BatchConn,
	src, dst control.LinkEnd, cfg control.BFD) error {

	if *cfg.Disable {
		return nil
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
	s, err := newBFDSend(conn, src.IA, dst.IA, src.Addr, dst.Addr, ifID, d.macFactory())
	if err != nil {
		return err
	}
	return d.addBFDController(ifID, s, cfg, m)
}

// getInterfaceState checks if there is a bfd session for the input interfaceID and
// returns InterfaceUp if the relevant bfdsession state is up, or if there is no BFD
// session. Otherwise, it returns InterfaceDown.
// @ preserves acc(d.Mem(), R5)
// @ decreases 0 if sync.IgnoreBlockingForTermination()
func (d *DataPlane) getInterfaceState(interfaceID uint16) control.InterfaceState {
	// @ unfold acc(d.Mem(), R5)
	// @ defer fold acc(d.Mem(), R5)
	bfdSessions := d.bfdSessions
	// @ ghost if bfdSessions != nil {
	// @ 	unfold acc(accBfdSession(d.bfdSessions), R20)
	// @ 	defer fold acc(accBfdSession(d.bfdSessions), R20)
	// @ }
	if bfdSession, ok := bfdSessions[interfaceID]; ok {
		// @ assert interfaceID in domain(d.bfdSessions)
		// @ assert bfdSession in range(d.bfdSessions)
		// @ assert bfdSession != nil
		// (VerifiedSCION) This checked used to be conjoined with 'ok' in the condition
		// of the if stmt above. We broke it down to perform intermediate asserts.
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
// @ preserves d.mtx.LockInv() == MutexInvariant!<d!>
// @ decreases 0 if sync.IgnoreBlockingForTermination()
func (d *DataPlane) AddSvc(svc addr.SVC, a netip.AddrPort) error {
	d.mtx.Lock()
	// @ unfold MutexInvariant!<d!>()
	// @ d.isRunningEq()
	defer d.mtx.Unlock()
	if !a.IsValid() {
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
		labels := serviceLabels(d.localIA, svc)
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
// @ decreases 0 if sync.IgnoreBlockingForTermination()
func (d *DataPlane) DelSvc(svc addr.SVC, a netip.AddrPort) error {
	d.mtx.Lock()
	defer d.mtx.Unlock()
	if !a.IsValid() {
		return emptyValue
	}
	// @ unfold acc(d.Mem(), R40)
	// @ ghost defer fold acc(d.Mem(), R40)
	if d.svc == nil {
		return nil
	}
	d.svc.DelSvc(svc, a)
	if d.Metrics != nil {
		labels := serviceLabels(d.localIA, svc)
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
// @ preserves d.mtx.LockInv() == MutexInvariant!<d!>
// @ decreases 0 if sync.IgnoreBlockingForTermination()
func (d *DataPlane) AddNextHop(ifID uint16, src, dst netip.AddrPort, cfg control.BFD,
	sibling string) error {

	d.mtx.Lock()
	defer d.mtx.Unlock()
	// @ unfold MutexInvariant!<d!>()
	// @ d.isRunningEq()
	// @ unfold d.Mem()
	// @ defer fold MutexInvariant!<d!>()
	// @ defer fold d.Mem()
	if d.IsRunning() {
		return modifyExisting
	}
	if !dst.IsValid() || !src.IsValid() {
		return emptyValue
	}
	err := d.addNextHopBFD(ifID, src, dst, cfg, sibling)
	if err != nil {
		return serrors.Wrap("adding next hop BFD", err, "if_id", ifID)
	}
	if d.internalNextHops == nil {
		d.internalNextHops = make(map[uint16]netip.AddrPort)
	}
	if _, exists := d.internalNextHops[ifID]; exists {
		return serrors.JoinNoStack(alreadySet, nil, "ifID", ifID)
	}
	// @ defer fold accAddr(d.internalNextHops)
	d.internalNextHops[ifID] = dst
	return nil
}

// AddNextHopBFD adds the BFD session for the next hop address.
// If the remote ifID belongs to an existing address, the existing
// BFD session will be re-used.
// @ trusted
// @ requires false
func (d *DataPlane) addNextHopBFD(ifID uint16, src, dst netip.AddrPort, cfg control.BFD,
	sibling string) error {

	if *cfg.Disable {
		return nil
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

	s, err := newBFDSend(d.internal, d.localIA, d.localIA, src, dst, 0, d.macFactory())
	if err != nil {
		return err
	}
	return d.addBFDController(ifID, s, cfg, m)
}

func max(a int, b int) int {
	if a > b {
		return a
	}
	return b
}

type RunConfig struct {
	NumProcessors         int
	NumSlowPathProcessors int
	BatchSize             int
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
// @ requires  d.mtx.LockInv() == MutexInvariant!<d!>
// @ requires  ctx != nil && ctx.Mem()
// contracts for IO-spec
// @ requires dp.Valid()
// @ requires d.DpAgreesWithSpec(dp)
// @ requires io.token(place) && dp.dp3s_iospec_ordered(state, place)
// @ #backend[moreJoins()]
func (d *DataPlane) Run(ctx context.Context, cfg *RunConfig) error {
	d.mtx.Lock()
	d.setRunning()
	d.initMetrics()

	processorQueueSize := max(
		len(d.interfaces)*cfg.BatchSize/cfg.NumProcessors,
		cfg.BatchSize)

	d.initPacketPool(cfg, processorQueueSize)
	procQs, fwQs, slowQs := initQueues(cfg, d.interfaces, processorQueueSize)

	for ifID, conn := range d.interfaces {
		go func(ifID uint16, conn BatchConn) {
			defer log.HandlePanic()
			d.runReceiver(ifID, conn, cfg, procQs)
		}(ifID, conn)
		go func(ifID uint16, conn BatchConn) {
			defer log.HandlePanic()
			d.runForwarder(ifID, conn, cfg, fwQs[ifID])
		}(ifID, conn)
	}
	for i := 0; i < cfg.NumProcessors; i++ {
		go func(i int) {
			defer log.HandlePanic()
			d.runProcessor(i, procQs[i], fwQs, slowQs[i%cfg.NumSlowPathProcessors])
		}(i)
	}
	for i := 0; i < cfg.NumSlowPathProcessors; i++ {
		go func(i int) {
			defer log.HandlePanic()
			d.runSlowPathProcessor(i, slowQs[i], fwQs)
		}(i)
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
	// @ invariant acc(d.Mem(), _) && d.WellConfigured()
	// @ invariant d.getValSvc() != nil
	// @ invariant d.getValForwardingMetrics() != nil
	// @ invariant 0 in d.getDomForwardingMetrics()
	// @ invariant d.getMacFactory() != nil
	// @ invariant dp.Valid()
	// @ invariant d.DpAgreesWithSpec(dp)
	// @ invariant acc(ioLockRun.LockP(), _)
	// @ invariant ioLockRun.LockInv() == SharedInv!< dp, ioSharedArgRun !>
	// @ decreases len(externals) - len(visited)
	for ifID, v := range externals /*@ with visited @*/ {
		cl :=
			// @ requires acc(&read, _) && read implements rc
			// @ requires acc(&d, _)
			// @ requires acc(d.Mem(), _) && d.WellConfigured()
			// @ requires d.getValSvc() != nil
			// @ requires d.getValForwardingMetrics() != nil
			// @ requires 0 in d.getDomForwardingMetrics()
			// @ requires i in d.getDomForwardingMetrics()
			// @ requires d.getMacFactory() != nil
			// @ requires c != nil && acc(c.Mem(), _)
			// contracts for IO-spec
			// @ requires dp.Valid()
			// @ requires d.DpAgreesWithSpec(dp)
			// @ requires acc(ioLock.LockP(), _)
			// @ requires ioLock.LockInv() == SharedInv!< dp, ioSharedArg !>
			func /*@ closure2 @*/ (i uint16, c BatchConn /*@, ghost ioLock gpointer[gsync.GhostMutex], ghost ioSharedArg SharedArg, ghost dp io.DataPlaneSpec @*/) {
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

	d.mtx.Unlock()
	<-ctx.Done()
	return nil
}

// initializePacketPool calculates the size of the packet pool based on the
// current dataplane settings and allocates all the buffers
func (d *DataPlane) initPacketPool(cfg *RunConfig, processorQueueSize int) {
	poolSize := len(d.interfaces)*cfg.BatchSize +
		(cfg.NumProcessors+cfg.NumSlowPathProcessors)*(processorQueueSize+1) +
		len(d.interfaces)*(2*cfg.BatchSize)

	log.Debug("Initialize packet pool of size", "poolSize", poolSize)
	d.packetPool = make(chan *packet, poolSize)
	pktBuffers := make([][bufSize]byte, poolSize)
	pktStructs := make([]packet, poolSize)
	for i := 0; i < poolSize; i++ {
		d.packetPool <- pktStructs[i].init(&pktBuffers[i])
	}
	// @ ghost if d.external != nil { fold acc(accBatchConn(d.external), R15) }
	// @ ghost if d.internalNextHops != nil { fold acc(accAddr(d.internalNextHops), R15) }
	// @ fold accForwardingMetrics(d.forwardingMetrics)
	// @ unfold acc(hideLocalIA(&d.localIA), R15)
	// @ assert d.dpSpecWellConfiguredLocalIA(dp)
	// @ assert d.dpSpecWellConfiguredNeighborIAs(dp)
	// @ assert d.dpSpecWellConfiguredLinkTypes(dp)
	// @ fold d.Mem()
	// @ reveal d.getDomExternal()
	// @ reveal d.WellConfigured()
	// @ assert reveal d.DpAgreesWithSpec(dp)
}

// initializes the processing routines and forwarders queues
func initQueues(cfg *RunConfig, interfaces map[uint16]BatchConn,
	processorQueueSize int) ([]chan *packet, map[uint16]chan *packet, []chan *packet) {

	procQs := make([]chan *packet, cfg.NumProcessors)
	for i := 0; i < cfg.NumProcessors; i++ {
		procQs[i] = make(chan *packet, processorQueueSize)
	}
	slowQs := make([]chan *packet, cfg.NumSlowPathProcessors)
	for i := 0; i < cfg.NumSlowPathProcessors; i++ {
		slowQs[i] = make(chan *packet, processorQueueSize)
	}
	fwQs := make(map[uint16]chan *packet)
	for ifID := range interfaces {
		fwQs[ifID] = make(chan *packet, cfg.BatchSize)
	}
	return procQs, fwQs, slowQs
}

func (d *DataPlane) runReceiver(ifID uint16, conn BatchConn, cfg *RunConfig,
	procQs []chan *packet) {

	log.Debug("Run receiver for", "interface", ifID)

	// Each receiver (therefore each input interface) has a unique random seed for the procID hash
	// function.
	hashSeed := fnv1aOffset32
	randomBytes := make([]byte, 4)
	if _, err := rand.Read(randomBytes); err != nil {
		panic("Error while generating random value")
	}
	for _, c := range randomBytes {
		hashSeed = hashFNV1a(hashSeed, c)
	}

	// A collection of socket messages, as the readBatch API expects them. We keep using the same
	// collection, call after call; only replacing the buffer.
	msgs := underlayconn.NewReadMessages(cfg.BatchSize)

	// An array of corresponding packet references. Each corresponds to one msg.
	// The packet owns the buffer that we set in the matching msg, plus the metadata that we'll add.
	packets := make([]*packet, cfg.BatchSize)

	numReusable := 0                     // unused buffers from previous loop
	metrics := d.forwardingMetrics[ifID] // If receiver exists, fw metrics exist too.

	enqueueForProcessing := func(size int, srcAddr *net.UDPAddr, pkt *packet) {
		sc := classOfSize(size)
		metrics[sc].InputPacketsTotal.Inc()
		metrics[sc].InputBytesTotal.Add(float64(size))

		procID, err := computeProcID(pkt.rawPacket, cfg.NumProcessors, hashSeed)
		if err != nil {
			log.Debug("Error while computing procID", "err", err)
			d.returnPacketToPool(pkt)
			metrics[sc].DroppedPacketsInvalid.Inc()
			return
		}

		pkt.rawPacket = pkt.rawPacket[:size] // Update size; readBatch does not.
		pkt.ingress = ifID
		pkt.srcAddr = srcAddr
		select {
		case procQs[procID] <- pkt:
		default:
			d.returnPacketToPool(pkt)
			metrics[sc].DroppedPacketsBusyProcessor.Inc()
		}
	}

	for d.IsRunning() {
		// collect packets.

		// Give a new buffer to the msgs elements that have been used in the previous loop.
		for i := 0; i < cfg.BatchSize-numReusable; i++ {
			p := <-d.packetPool
			p.reset()
			packets[i] = p
			msgs[i].Buffers[0] = p.rawPacket
		}

		// Fill the packets
		numPkts, err := conn.ReadBatch(msgs)
		numReusable = len(msgs) - numPkts
		if err != nil {
			log.Debug("Error while reading batch", "interfaceID", ifID, "err", err)
			continue
		}
		for i, msg := range msgs[:numPkts] {
			enqueueForProcessing(msg.N, msg.Addr.(*net.UDPAddr), packets[i])
		}
	}
}

func computeProcID(data []byte, numProcRoutines int, hashSeed uint32) (uint32, error) {
	if len(data) < slayers.CmnHdrLen {
		return 0, errShortPacket
	}
	dstHostAddrLen := slayers.AddrType(data[9] >> 4 & 0xf).Length()
	srcHostAddrLen := slayers.AddrType(data[9] & 0xf).Length()
	addrHdrLen := 2*addr.IABytes + srcHostAddrLen + dstHostAddrLen
	if len(data) < slayers.CmnHdrLen+addrHdrLen {
		return 0, errShortPacket
	}

	s := hashSeed

	// inject the flowID
	s = hashFNV1a(s, data[1]&0xF) // The left 4 bits aren't part of the flowID.
	for _, c := range data[2:4] {
		s = hashFNV1a(s, c)
	}

	// Inject the src/dst addresses
	for _, c := range data[slayers.CmnHdrLen : slayers.CmnHdrLen+addrHdrLen] {
		s = hashFNV1a(s, c)
	}

	return s % uint32(numProcRoutines), nil
}

func (d *DataPlane) returnPacketToPool(pkt *packet) {
	d.packetPool <- pkt
}

func (d *DataPlane) runProcessor(id int, q <-chan *packet,
	fwQs map[uint16]chan *packet, slowQ chan<- *packet) {

	log.Debug("Initialize processor with", "id", id)
	processor := newPacketProcessor(d)
	for d.IsRunning() {
		p, ok := <-q
		if !ok {
			continue
		}
		disp := processor.processPkt(p)

		sc := classOfSize(len(p.rawPacket))
		metrics := d.forwardingMetrics[p.ingress][sc]
		metrics.ProcessedPackets.Inc()

		switch disp {
		case pForward:
			// Normal processing proceeds.
		case pSlowPath:
			// Not an error, processing continues on the slow path.
			select {
			case slowQ <- p:
			default:
				metrics.DroppedPacketsBusySlowPath.Inc()
				d.returnPacketToPool(p)
			}
			continue
		case pDone: // Packets that don't need more processing (e.g. BFD)
			d.returnPacketToPool(p)
			continue
		case pDiscard: // Everything else
			metrics.DroppedPacketsInvalid.Inc()
			d.returnPacketToPool(p)
			continue
		default: // Newly added dispositions need to be handled.
			log.Debug("Unknown packet disposition", "disp", disp)
			d.returnPacketToPool(p)
			continue
		}
		fwCh, ok := fwQs[p.egress]
		if !ok {
			log.Debug("Error determining forwarder. Egress is invalid", "egress", p.egress)
			metrics.DroppedPacketsInvalid.Inc()
			d.returnPacketToPool(p)
			continue
		}

		select {
		case fwCh <- p:
		default:
			d.returnPacketToPool(p)
			metrics.DroppedPacketsBusyForwarder.Inc()
		}
	}
}

func (d *DataPlane) runSlowPathProcessor(id int, q <-chan *packet,
	fwQs map[uint16]chan *packet) {

	log.Debug("Initialize slow-path processor with", "id", id)
	processor := newSlowPathProcessor(d)
	for d.IsRunning() {
		p, ok := <-q
		if !ok {
			continue
		}
		err := processor.processPacket(p)
		sc := classOfSize(len(p.rawPacket))
		metrics := d.forwardingMetrics[p.ingress][sc]
		if err != nil {
			log.Debug("Error processing packet", "err", err)
			metrics.DroppedPacketsInvalid.Inc()
			d.returnPacketToPool(p)
			continue
		}
		fwCh, ok := fwQs[p.egress]
		if !ok {
			log.Debug("Error determining forwarder. Egress is invalid", "egress", p.egress)
			d.returnPacketToPool(p)
			continue
		}
		select {
		case fwCh <- p:
		default:
			d.returnPacketToPool(p)
		}
	}
}

func newSlowPathProcessor(d *DataPlane) *slowPathPacketProcessor {
	p := &slowPathPacketProcessor{
		d:              d,
		buffer:         gopacket.NewSerializeBuffer(),
		macInputBuffer: make([]byte, spao.MACBufferSize),
		drkeyProvider: &drkeyutil.FakeProvider{
			EpochDuration:    drkeyutil.LoadEpochDuration(),
			AcceptanceWindow: drkeyutil.LoadAcceptanceWindow(),
		},
		optAuth:      slayers.PacketAuthOption{EndToEndOption: new(slayers.EndToEndOption)},
		validAuthBuf: make([]byte, 16),
	}
	p.scionLayer.RecyclePaths()
	return p
}

type slowPathPacketProcessor struct {
	d      *DataPlane
	pkt    *packet
	buffer gopacket.SerializeBuffer

	scionLayer slayers.SCION
	hbhLayer   slayers.HopByHopExtnSkipper
	e2eLayer   slayers.EndToEndExtnSkipper
	lastLayer  gopacket.DecodingLayer
	path       *scion.Raw

	// macInputBuffer avoid allocating memory during processing.
	macInputBuffer []byte

	// optAuth is a reusable Packet Authenticator Option
	optAuth slayers.PacketAuthOption
	// validAuthBuf is a reusable buffer for the authentication tag
	// to be used in the hasValidAuth() method.
	validAuthBuf []byte

	// DRKey key derivation for SCMP authentication
	drkeyProvider drkeyProvider
}

func (p *slowPathPacketProcessor) reset() {
	if err := p.buffer.Clear(); err != nil {
		// The serializeBuffer returned by NewSerializeBuffer isn't actually capable of failing to
		// clear, so planning on doing something about it is pointless (and what might that be?).
		panic(fmt.Sprintf("Error while clearing buffer: %v", err))
	}
	p.path = nil
	p.hbhLayer = slayers.HopByHopExtnSkipper{}
	p.e2eLayer = slayers.EndToEndExtnSkipper{}
}

func (p *slowPathPacketProcessor) processPacket(pkt *packet) error {
	var err error
	p.reset()
	p.pkt = pkt

	p.lastLayer, err = decodeLayers(pkt.rawPacket, &p.scionLayer, &p.hbhLayer, &p.e2eLayer)
	if err != nil {
		return err
	}
	pathType := p.scionLayer.PathType
	switch pathType {
	case scion.PathType:
		var ok bool
		p.path, ok = p.scionLayer.Path.(*scion.Raw)
		if !ok {
			return malformedPath
		}
	case epic.PathType:
		epicPath, ok := p.scionLayer.Path.(*epic.Path)
		if !ok {
			return malformedPath
		}
		p.path = epicPath.ScionPath
		if p.path == nil {
			return malformedPath
		}
	default:
		//unsupported path type
		return serrors.New("Path type not supported for slow-path", "type", pathType)
	}

	s := pkt.slowPathRequest
	switch s.typ {
	case slowPathSCMP: //SCMP
		var layer gopacket.SerializableLayer
		switch s.scmpType {
		case slayers.SCMPTypeParameterProblem:
			layer = &slayers.SCMPParameterProblem{Pointer: s.pointer}
		case slayers.SCMPTypeDestinationUnreachable:
			layer = &slayers.SCMPDestinationUnreachable{}
		case slayers.SCMPTypeExternalInterfaceDown:
			layer = &slayers.SCMPExternalInterfaceDown{IA: p.d.localIA,
				IfID: uint64(p.pkt.egress)}
		case slayers.SCMPTypeInternalConnectivityDown:
			layer = &slayers.SCMPInternalConnectivityDown{IA: p.d.localIA,
				Ingress: uint64(p.pkt.ingress), Egress: uint64(p.pkt.egress)}
		}
		return p.packSCMP(s.scmpType, s.code, layer, true)

	case slowPathRouterAlertIngress: //Traceroute
		return p.handleSCMPTraceRouteRequest(p.pkt.ingress)
	case slowPathRouterAlertEgress: //Traceroute
		return p.handleSCMPTraceRouteRequest(p.pkt.egress)
	default:
		panic("Unsupported slow-path type")
	}
}

func updateOutputMetrics(metrics interfaceMetrics, packets []*packet) {
	// We need to collect stats by traffic type and size class.
	// Try to reduce the metrics lookup penalty by using some
	// simpler staging data structure.
	writtenPkts := [ttMax][maxSizeClass]int{}
	writtenBytes := [ttMax][maxSizeClass]int{}
	for _, p := range packets {
		s := len(p.rawPacket)
		sc := classOfSize(s)
		tt := p.trafficType
		writtenPkts[tt][sc]++
		writtenBytes[tt][sc] += s
	}
	for t := ttOther; t < ttMax; t++ {
		for sc := minSizeClass; sc < maxSizeClass; sc++ {
			if writtenPkts[t][sc] > 0 {
				metrics[sc].Output[t].OutputPacketsTotal.Add(float64(writtenPkts[t][sc]))
				metrics[sc].Output[t].OutputBytesTotal.Add(float64(writtenBytes[t][sc]))
			}
		}
	}
}

func (d *DataPlane) runForwarder(ifID uint16, conn BatchConn, cfg *RunConfig, c <-chan *packet) {

	log.Debug("Initialize forwarder for", "interface", ifID)

	// We use this somewhat like a ring buffer.
	pkts := make([]*packet, cfg.BatchSize)

	// We use this as a temporary buffer, but allocate it just once
	// to save on garbage handling.
	msgs := make(underlayconn.Messages, cfg.BatchSize)
	for i := range msgs {
		msgs[i].Buffers = make([][]byte, 1)
	}

	metrics := d.forwardingMetrics[ifID]

	toWrite := 0
	for d.IsRunning() {
		toWrite += readUpTo(c, cfg.BatchSize-toWrite, toWrite == 0, pkts[toWrite:])

		// Turn the packets into underlay messages that WriteBatch can send.
		for i, p := range pkts[:toWrite] {
			msgs[i].Buffers[0] = p.rawPacket
			msgs[i].Addr = nil
			if len(p.dstAddr.IP) != 0 {
				msgs[i].Addr = p.dstAddr
			}
		}
		written, _ := conn.WriteBatch(msgs[:toWrite], 0)
		if written < 0 {
			// WriteBatch returns -1 on error, we just consider this as
			// 0 packets written
			written = 0
		}

		updateOutputMetrics(metrics, pkts[:written])

		for _, p := range pkts[:written] {
			d.returnPacketToPool(p)
		}

		if written != toWrite {
			// Only one is dropped at this time. We'll retry the rest.
			sc := classOfSize(len(pkts[written].rawPacket))
			metrics[sc].DroppedPacketsInvalid.Inc()
			d.returnPacketToPool(pkts[written])
			toWrite -= (written + 1)
			// Shift the leftovers to the head of the buffers.
			for i := 0; i < toWrite; i++ {
				pkts[i] = pkts[i+written+1]
			}

		} else {
			toWrite = 0
		}
	}
}

func readUpTo(c <-chan *packet, n int, needsBlocking bool, pkts []*packet) int {
	i := 0
	if needsBlocking {
		p, ok := <-c
		if !ok {
			return i
		}
		pkts[i] = p
		i++
	}

	for ; i < n; i++ {
		select {
		case p, ok := <-c:
			if !ok {
				return i
			}
			pkts[i] = p
		default:
			return i
		}

	}
	return i
}

func newPacketProcessor(d *DataPlane) *scionPacketProcessor {
	p := &scionPacketProcessor{
		d:              d,
		buffer:         gopacket.NewSerializeBuffer(),
		mac:            d.macFactory(),
		macInputBuffer: make([]byte, max(path.MACBufferSize, libepic.MACBufferSize)),
	}
	// @ fold sl.Bytes(p.macBuffers.scionInput, 0, len(p.macBuffers.scionInput))
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
// @ preserves let ubuf := p.sInitBufferUBuf() in
// @ 	acc(sl.Bytes(ubuf, 0, len(ubuf)), writePerm)
// @ ensures   p.sInitD()         == old(p.sInitD())
// @ ensures   p.getIngressID()   == old(p.getIngressID())
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
	p.pkt = nil
	//p.scionLayer // cannot easily be reset
	p.path = nil
	p.hopField = path.HopField{}
	p.infoField = path.InfoField{}
	p.effectiveXover = false
	p.peering = false
	if err := p.buffer.Clear(); err != nil {
		// The serializeBuffer returned by NewSerializeBuffer isn't actually capable of failing to
		// clear, so planning on doing something about it is pointless (and what might that be?).
		panic(fmt.Sprintf("Error while clearing buffer: %v", err))
	}
	p.mac.Reset()
	p.cachedMac = nil
	// Reset hbh layer
	p.hbhLayer = slayers.HopByHopExtnSkipper{}
	// Reset e2e layer
	p.e2eLayer = slayers.EndToEndExtnSkipper{}
	return nil
}

// Convenience function to log an error and return the pDiscard disposition.
// We do almost nothing with errors, so, we shouldn't invest in creating them.
func errorDiscard(ctx ...any) disposition {
	log.Debug("Discarding packet", ctx...)
	return pDiscard
}

// @ requires p.sInit()
// @ requires sl.Bytes(rawPkt, 0, len(rawPkt))
// @ requires acc(srcAddr.Mem(), _)
// @ requires let d := p.sInitD() in
// @ 	acc(d.Mem(), _) &&
// @ 	d.WellConfigured()        &&
// @ 	d.getValSvc() != nil      &&
// @ 	d.getValForwardingMetrics() != nil &&
// @ 	d.DpAgreesWithSpec(dp)
// @ requires let ubuf := p.sInitBufferUBuf() in
// @ 	acc(sl.Bytes(ubuf, 0, len(ubuf)), writePerm)
// @ ensures  p.sInit()
// @ ensures  acc(p.sInitD().Mem(), _)
// @ ensures  p.sInitD() == old(p.sInitD())
// @ ensures  p.getIngressID() == old(p.getIngressID())
// @ ensures  p.sInitD().validResult(respr, addrAliasesPkt)
// @ ensures  acc(sl.Bytes(rawPkt, 0, len(rawPkt)), 1 - R15)
// @ ensures  addrAliasesPkt ==> (
// @ 	respr.OutAddr != nil &&
// @ 	(acc(respr.OutAddr.Mem(), R15) --* acc(sl.Bytes(rawPkt, 0, len(rawPkt)), R15)))
// @ ensures  !addrAliasesPkt ==> acc(sl.Bytes(rawPkt, 0, len(rawPkt)), R15)
// @ ensures let ubuf := p.sInitBufferUBuf() in
// @ 	acc(sl.Bytes(ubuf, 0, len(ubuf)), writePerm)
// @ ensures respr.OutPkt != nil ==>
// @ 	(respr.OutPkt === rawPkt || respr.OutPkt === p.sInitBufferUBuf())
// @ ensures  reserr != nil ==> reserr.ErrorMem()
// contracts for IO-spec
// @ requires dp.Valid()
// @ requires acc(ioLock.LockP(), _)
// @ requires ioLock.LockInv() == SharedInv!< dp, ioSharedArg !>
// @ requires let absPkt := absIO_val(rawPkt, p.getIngressID()) in
// @ 	absPkt.isIO_val_Pkt2 ==> ElemWitness(ioSharedArg.IBufY, path.ifsToIO_ifs(p.getIngressID()), absPkt.IO_val_Pkt2_2)
// @ ensures  respr.OutPkt != nil ==>
// @ 	newAbsPkt == absIO_val(respr.OutPkt, respr.EgressID)
// @ ensures  (respr.OutPkt == nil) == (newAbsPkt == io.IO_val_Unit{})
// @ ensures  newAbsPkt.isIO_val_Pkt2 ==>
// @ 	ElemWitness(ioSharedArg.OBufY, newAbsPkt.IO_val_Pkt2_1, newAbsPkt.IO_val_Pkt2_2)
// @ ensures  reserr != nil && respr.OutPkt != nil ==> newAbsPkt.isIO_val_Unsupported
// @ decreases 0 if sync.IgnoreBlockingForTermination()
// @ #backend[moreJoins(1)]
func (p *scionPacketProcessor) processPkt(pkt *packet) disposition {
	if err := p.reset(); err != nil {
		return errorDiscard("error", err)
	}
	p.pkt = pkt

	// parse SCION header and skip extensions;
	var err error
	p.lastLayer, err = decodeLayers(pkt.rawPacket, &p.scionLayer, &p.hbhLayer, &p.e2eLayer)
	if err != nil {
		return errorDiscard("error", err)
	}

	pld := p.lastLayer.LayerPayload()

	// @ ghost llStart := 0
	// @ ghost llEnd := len(p.rawPkt)
	// @ ghost mustCombineRanges := lastLayerIdx != -1 && !offsets[lastLayerIdx].isNil
	// @ ghost var o offsetPair
	// @ ghost if lastLayerIdx == -1 {
	// @ 	ub = p.rawPkt
	// @ } else {
	// @ 	if offsets[lastLayerIdx].isNil {
	// @ 		ub = nil
	// @ 		sl.NilAcc_Bytes()
	// @ 	} else {
	// @ 		o = offsets[lastLayerIdx]
	// @ 		ub = p.rawPkt[o.start:o.end]
	// @ 		llStart = o.start
	// @ 		llEnd = o.end
	// @ 		sl.SplitRange_Bytes(p.rawPkt, o.start, o.end, HalfPerm)
	// @ 	}
	// @ }
	// @ hasHbhLayer := processed[0]
	// @ oHbh := offsets[0]
	// @ ubHbhLayer = hasHbhLayer && !oHbh.isNil ? p.rawPkt[oHbh.start:oHbh.end] : ([]byte)(nil)
	// @ hasE2eLayer := processed[1]
	// @ oE2e := offsets[1]
	// @ ubE2eLayer = hasE2eLayer && !oE2e.isNil ? p.rawPkt[oE2e.start:oE2e.end] : ([]byte)(nil)
	// @ assert processed[0] ==> p.hbhLayer.Mem(ubHbhLayer)
	// @ assert processed[1] ==> p.e2eLayer.Mem(ubE2eLayer)
	// @ assert acc(sl.Bytes(ub, 0, len(ub)), HalfPerm)
	pld /*@ , start, end @*/ := p.lastLayer.LayerPayload( /*@ ub @*/ )
	// @ sl.SplitRange_Bytes(ub, start, end, HalfPerm)
	// @ sl.NilAcc_Bytes()
	pathType := /*@ unfolding p.scionLayer.Mem(rawPkt) in @*/ p.scionLayer.PathType
	switch pathType {
	case empty.PathType:
		// @ ghost sl.SplitRange_Bytes(p.rawPkt, o.start, o.end, HalfPerm)
		// @ sl.SplitRange_Bytes(ub, start, end, HalfPerm)
		// @ ghost if mustCombineRanges { ghost defer sl.CombineRange_Bytes(p.rawPkt, o.start, o.end, writePerm) }
		if p.lastLayer.NextLayerType( /*@ ub @*/ ) == layers.LayerTypeBFD {
			// @ ResetDecodingLayers(&p.scionLayer, &p.hbhLayer, &p.e2eLayer, ubScionLayer, ubHbhLayer, ubE2eLayer, true, hasHbhLayer, hasE2eLayer)
			// @ defer fold p.sInit()
			// @ defer fold p.d.validResult(processResult{}, false)
			// @ ghost defer sl.CombineRange_Bytes(ub, start, end, writePerm)
			return p.processIntraBFD(pld)
		}
		// @ establishMemUnsupportedPathTypeNextHeader()
		// @ defer fold p.sInit()
		// @ defer fold p.d.validResult(processResult{}, false)
		// @ ghost defer ResetDecodingLayers(&p.scionLayer, &p.hbhLayer, &p.e2eLayer, ubScionLayer, ubHbhLayer, ubE2eLayer, true, hasHbhLayer, hasE2eLayer)
		// @ ghost defer sl.CombineRange_Bytes(ub, start, end, writePerm)
		return errorDiscard("error", unsupportedPathTypeNextHeader)

	case onehop.PathType:
		if p.lastLayer.NextLayerType( /*@ ub @*/ ) == layers.LayerTypeBFD {
			// @ ghost sl.SplitRange_Bytes(p.rawPkt, o.start, o.end, HalfPerm)
			// @ sl.SplitRange_Bytes(ub, start, end, HalfPerm)
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
				return errorDiscard("error", malformedPath)
			}
			// @ defer fold p.sInit()
			// @ defer fold p.d.validResult(processResult{}, false)
			// @ ghost defer ResetDecodingLayers(&p.scionLayer, &p.hbhLayer, &p.e2eLayer, ubScionLayer, ubHbhLayer, ubE2eLayer, true, hasHbhLayer, hasE2eLayer)
			return p.processInterBFD(ohp, pld)
		}
		// @ sl.CombineRange_Bytes(ub, start, end, HalfPerm)
		// @ ghost if lastLayerIdx >= 0 && !offsets[lastLayerIdx].isNil {
		// @ 	o := offsets[lastLayerIdx]
		// @ 	sl.CombineRange_Bytes(p.rawPkt, o.start, o.end, HalfPerm)
		// @ }
		// @ assert sl.Bytes(p.rawPkt, 0, len(p.rawPkt))
		// @ unfold acc(p.d.Mem(), _)
		// @ assert reveal p.scionLayer.EqPathType(p.rawPkt)
		// @ assert !(reveal slayers.IsSupportedPkt(p.rawPkt))
		v1, v2 /*@, aliasesPkt, newAbsPkt @*/ := p.processOHP()
		// @ ResetDecodingLayers(&p.scionLayer, &p.hbhLayer, &p.e2eLayer, ubScionLayer, ubHbhLayer, ubE2eLayer, true, hasHbhLayer, hasE2eLayer)
		// @ fold p.sInit()
		return v1, v2 /*@, aliasesPkt, newAbsPkt @*/
	case scion.PathType:
		// @ sl.CombineRange_Bytes(ub, start, end, HalfPerm)
		// @ ghost if lastLayerIdx >= 0 && !offsets[lastLayerIdx].isNil {
		// @ 	o := offsets[lastLayerIdx]
		// @ 	sl.CombineRange_Bytes(p.rawPkt, o.start, o.end, HalfPerm)
		// @ }
		// @ assert sl.Bytes(p.rawPkt, 0, len(p.rawPkt))
		v1, v2 /*@ , addrAliasesPkt, newAbsPkt @*/ := p.processSCION( /*@ p.rawPkt, ub == nil, llStart, llEnd, ioLock, ioSharedArg, dp @*/ )
		// @ ResetDecodingLayers(&p.scionLayer, &p.hbhLayer, &p.e2eLayer, ubScionLayer, ubHbhLayer, ubE2eLayer, v2 == nil, hasHbhLayer, hasE2eLayer)
		// @ fold p.sInit()
		return v1, v2 /*@, addrAliasesPkt, newAbsPkt @*/
	case epic.PathType:
		// @ TODO()
		v1, v2 := p.processEPIC()
		// @ fold p.sInit()
		return v1, v2 /*@, false, io.IO_val_Unit{} @*/
	default:
		// @ ghost if mustCombineRanges { ghost defer sl.CombineRange_Bytes(p.rawPkt, o.start, o.end, HalfPerm) }
		// @ ResetDecodingLayers(&p.scionLayer, &p.hbhLayer, &p.e2eLayer, ubScionLayer, ubHbhLayer, ubE2eLayer, true, hasHbhLayer, hasE2eLayer)
		// @ sl.CombineRange_Bytes(ub, start, end, HalfPerm)
		// @ fold p.d.validResult(processResult{}, false)
		// @ fold p.sInit()
		// @ establishMemUnsupportedPathType()
		return errorDiscard("error", unsupportedPathType)
	}
}

// @ requires  acc(&p.d, R20)
// @ requires  acc(&p.ingressID, R20)
// @ requires  acc(p.d.Mem(), _)
// @ requires  p.bfdLayer.NonInitMem()
// @ preserves sl.Bytes(data, 0, len(data))
// @ ensures   acc(&p.d, R20)
// @ ensures   acc(&p.ingressID, R20)
// @ ensures   p.bfdLayer.NonInitMem()
// @ ensures   err != nil ==> err.ErrorMem()
// @ decreases 0 if sync.IgnoreBlockingForTermination()
func (p *scionPacketProcessor) processInterBFD(oh *onehop.Path, data []byte) disposition {
	// @ unfold acc(p.d.Mem(), _)
	// @ ghost if p.d.bfdSessions != nil { unfold acc(accBfdSession(p.d.bfdSessions), _) }
	if len(p.d.bfdSessions) == 0 {
		// @ establishMemNoBFDSessionConfigured()
		return errorDiscard("error", noBFDSessionConfigured)
	}

	bfd := &p.bfdLayer
	// @ gopacket.AssertInvariantNilDecodeFeedback()
	if err := bfd.DecodeFromBytes(data, gopacket.NilDecodeFeedback); err != nil {
		return errorDiscard("error", err)
	}

	if v, ok := p.d.bfdSessions[p.pkt.ingress]; ok {
		// @ assert v in range(p.d.bfdSessions)
		v.ReceiveMessage(bfd)
		return pDiscard // All's fine. That packet's journey ends here.
	}
	// @ bfd.DowngradePerm(data)
	// @ establishMemNoBFDSessionFound()
	return errorDiscard("error", noBFDSessionFound)
}

// @ requires  acc(&p.d, R20)
// @ requires  acc(&p.srcAddr, R20) && acc(p.srcAddr.Mem(), _)
// @ requires  p.bfdLayer.NonInitMem()
// @ requires  acc(p.d.Mem(), _)
// @ requires  sl.Bytes(data, 0, len(data))
// @ ensures   acc(&p.d, R20)
// @ ensures   acc(&p.srcAddr, R20)
// @ ensures   p.bfdLayer.NonInitMem()
// @ ensures   sl.Bytes(data, 0, len(data))
// @ ensures   res != nil ==> res.ErrorMem()
// @ decreases 0 if sync.IgnoreBlockingForTermination()
func (p *scionPacketProcessor) processIntraBFD(data []byte) disposition {
	// @ unfold acc(p.d.Mem(), _)
	// @ ghost if p.d.bfdSessions != nil { unfold acc(accBfdSession(p.d.bfdSessions), _) }
	if len(p.d.bfdSessions) == 0 {
		// @ establishMemNoBFDSessionConfigured()
		return errorDiscard("error", noBFDSessionConfigured)
	}

	bfd := &p.bfdLayer
	// @ gopacket.AssertInvariantNilDecodeFeedback()
	if err := bfd.DecodeFromBytes(data, gopacket.NilDecodeFeedback); err != nil {
		return errorDiscard("error", err)
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
	// @ decreases len(p.d.internalNextHops) - len(keys)
	src := p.pkt.srcAddr.AddrPort() // POSSIBLY EXPENSIVE CONVERSION
	for k, v := range p.d.internalNextHops {
		// @ assert acc(&p.d.internalNextHops, _)
		// @ assert forall a *net.UDPAddr :: { a in range(m) } a in range(m) ==> acc(a.Mem(), _)
		// @ assert acc(v.Mem(), _)
		// @ unfold acc(v.Mem(), _)
		// @ unfold acc(p.srcAddr.Mem(), _)
		if src == v {
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
		return pDiscard // All's fine. That packet's journey ends here.
	}
	// @ bfd.DowngradePerm(data)
	// @ establishMemNoBFDSessionFound()
	return errorDiscard("error", noBFDSessionFound)
}

// @ requires  0 <= startLL && startLL <= endLL && endLL <= len(ub)
// @ requires  acc(&p.d, R5) && acc(p.d.Mem(), _) && p.d.WellConfigured()
// @ requires  p.d.getValSvc() != nil
// The ghost param ub here allows us to introduce a bound variable to p.rawPkt,
// which slightly simplifies the spec
// @ requires  acc(&p.rawPkt, R1) && ub === p.rawPkt
// @ requires  acc(&p.path)
// @ requires  p.scionLayer.Mem(ub)
// @ requires  sl.Bytes(ub, 0, len(ub))
// @ requires  acc(&p.segmentChange) && !p.segmentChange
// @ requires  acc(&p.buffer, R10) && p.buffer != nil && p.buffer.Mem()
// @ requires  sl.Bytes(p.buffer.UBuf(), 0, len(p.buffer.UBuf()))
// @ requires  acc(&p.ingressID, R10)
// @ preserves acc(&p.srcAddr, R10) && acc(p.srcAddr.Mem(), _)
// @ preserves acc(&p.lastLayer, R10)
// @ preserves p.lastLayer != nil
// @ preserves (p.lastLayer !== &p.scionLayer && llIsNil) ==>
// @ 	acc(p.lastLayer.Mem(nil), R10)
// @ preserves (p.lastLayer !== &p.scionLayer && !llIsNil) ==>
// @ 	acc(p.lastLayer.Mem(ub[startLL:endLL]), R10)
// @ preserves &p.scionLayer === p.lastLayer ==>
// @ 	!llIsNil && startLL == 0 && endLL == len(ub)
// @ preserves acc(&p.infoField)
// @ preserves acc(&p.hopField)
// @ preserves acc(&p.mac, R10) && p.mac != nil && p.mac.Mem()
// @ preserves acc(&p.macBuffers.scionInput, R10)
// @ preserves sl.Bytes(p.macBuffers.scionInput, 0, len(p.macBuffers.scionInput))
// @ preserves acc(&p.cachedMac)
// @ ensures   acc(&p.segmentChange)
// @ ensures   acc(&p.ingressID, R10)
// @ ensures   acc(&p.d, R5)
// @ ensures   acc(&p.path)
// @ ensures   acc(&p.rawPkt, R1)
// @ ensures   acc(sl.Bytes(ub, 0, len(ub)), 1 - R15)
// @ ensures   p.d.validResult(respr, addrAliasesPkt)
// @ ensures   addrAliasesPkt ==> (
// @ 	respr.OutAddr != nil &&
// @ 	(acc(respr.OutAddr.Mem(), R15) --* acc(sl.Bytes(ub, 0, len(ub)), R15)))
// @ ensures   !addrAliasesPkt ==> acc(sl.Bytes(ub, 0, len(ub)), R15)
// @ ensures   acc(&p.buffer, R10) && p.buffer != nil && p.buffer.Mem()
// @ ensures   reserr == nil ==> p.scionLayer.Mem(ub)
// @ ensures   reserr != nil ==> p.scionLayer.NonInitMem()
// @ ensures   sl.Bytes(p.buffer.UBuf(), 0, len(p.buffer.UBuf()))
// @ ensures respr.OutPkt != nil ==>
// @ 	(respr.OutPkt === ub || respr.OutPkt === p.buffer.UBuf())
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// contracts for IO-spec
// @ requires  p.d.DpAgreesWithSpec(dp)
// @ requires  dp.Valid()
// @ requires  (typeOf(p.scionLayer.GetPath(ub)) == *scion.Raw) ==>
// @ 	p.scionLayer.EqAbsHeader(ub) && p.scionLayer.ValidScionInitSpec(ub)
// @ requires  p.scionLayer.EqPathType(ub)
// @ requires  acc(ioLock.LockP(), _)
// @ requires  ioLock.LockInv() == SharedInv!< dp, ioSharedArg !>
// @ requires  let absPkt := absIO_val(p.rawPkt, p.ingressID) in
// @ 	absPkt.isIO_val_Pkt2 ==> ElemWitness(ioSharedArg.IBufY, path.ifsToIO_ifs(p.ingressID), absPkt.IO_val_Pkt2_2)
// @ ensures   reserr == nil && newAbsPkt.isIO_val_Pkt2 ==>
// @ 	ElemWitness(ioSharedArg.OBufY, newAbsPkt.IO_val_Pkt2_1, newAbsPkt.IO_val_Pkt2_2)
// @ ensures   respr.OutPkt != nil ==>
// @ 	newAbsPkt == absIO_val(respr.OutPkt, respr.EgressID)
// @ ensures   reserr != nil && respr.OutPkt != nil ==>
// @ 	newAbsPkt.isIO_val_Unsupported
// @ ensures  (respr.OutPkt == nil) == (newAbsPkt == io.IO_val_Unit{})
// @ decreases 0 if sync.IgnoreBlockingForTermination()
func (p *scionPacketProcessor) processSCION( /*@ ghost ub []byte, ghost llIsNil bool, ghost startLL int, ghost endLL int, ghost ioLock gpointer[gsync.GhostMutex], ghost ioSharedArg SharedArg, ghost dp io.DataPlaneSpec @*/ ) (disp disposition /*@ , ghost addrAliasesPkt bool, ghost newAbsPkt io.IO_val @*/)  {

	var ok bool
	// @ unfold acc(p.scionLayer.Mem(ub), R20)
	p.path, ok = p.scionLayer.Path.(*scion.Raw)
	// @ fold acc(p.scionLayer.Mem(ub), R20)
	if !ok {
		// TODO(lukedirtwalker) parameter problem invalid path?
		// @ p.scionLayer.DowngradePerm(ub)
		// @ establishMemMalformedPath()
		// @ fold p.d.validResult(processResult{}, false)
		return errorDiscard("error", malformedPath)
	}
	return p.process( /*@ ub, llIsNil, startLL, endLL , ioLock, ioSharedArg, dp @*/ )
}

// @ trusted
// @ requires false
func (p *scionPacketProcessor) processEPIC() disposition {

	epicPath, ok := p.scionLayer.Path.(*epic.Path)
	if !ok {
		return errorDiscard("error", malformedPath)
	}

	p.path = epicPath.ScionPath
	if p.path == nil {
		return errorDiscard("error", malformedPath)
	}

	isPenultimate := p.path.IsPenultimateHop()
	isLast := p.path.IsLastHop()

	disp := p.process()
	if disp != pForward {
		return disp
	}

	if isPenultimate || isLast {
		firstInfo, err := p.path.GetInfoField(0)
		if err != nil {
			return errorDiscard("error", err)
		}

		timestamp := time.Unix(int64(firstInfo.Timestamp), 0)
		err = libepic.VerifyTimestamp(timestamp, epicPath.PktID.Timestamp, time.Now())
		if err != nil {
			// TODO(mawyss): Send back SCMP packet
			return errorDiscard("error", err)
		}

		HVF := epicPath.PHVF
		if isLast {
			HVF = epicPath.LHVF
		}
		err = libepic.VerifyHVF(p.cachedMac, epicPath.PktID,
			&p.scionLayer, firstInfo.Timestamp, HVF, p.macInputBuffer[:libepic.MACBufferSize])
		if err != nil {
			// TODO(mawyss): Send back SCMP packet
			return errorDiscard("error", err)
		}
	}

	// LGTM
	return pForward
}

// scionPacketProcessor processes packets. It contains pre-allocated per-packet
// mutable state and context information which should be reused.
type scionPacketProcessor struct {
	// d is a reference to the dataplane instance that initiated this processor.
	d *DataPlane
	// pkt is the packet currently being processed by this processor.
	pkt *packet
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
	// effectiveXover indicates if a cross-over segment change was done during processing.
	effectiveXover bool

	// peering indicates that the hop field being processed is a peering hop field.
	peering bool

	// cachedMac contains the full 16 bytes of the MAC. Will be set during processing.
	// For a hop performing an Xover, it is the MAC corresponding to the down segment.
	cachedMac []byte
	// macInputBuffer avoid allocating memory during processing.
	macInputBuffer []byte

	// bfdLayer is reusable buffer for parsing BFD messages
	bfdLayer layers.BFD
}

type slowPathType uint8

const (
	slowPathSCMP slowPathType = iota
	slowPathRouterAlertIngress
	slowPathRouterAlertEgress
)

// @ requires acc(&p.d, R50) && acc(p.d.Mem(), _)
// @ requires acc(p.scionLayer.Mem(ub), R4)
// @ requires 0 <= startLL && startLL <= endLL && endLL <= len(ub)
// @ requires  p.scionLayer.ValidPathMetaData(ub)
// @ requires  sl.Bytes(ub, 0, len(ub))
// @ requires  acc(&p.ingressID,  R45)
// @ requires  acc(&p.buffer, R50) && p.buffer != nil && p.buffer.Mem()
// @ requires  sl.Bytes(p.buffer.UBuf(), 0, len(p.buffer.UBuf()))
// @ requires  cause != nil ==> cause.ErrorMem()
// @ preserves ubLL == nil || ubLL === ub[startLL:endLL]
// @ preserves acc(&p.lastLayer, R55) && p.lastLayer != nil
// @ preserves &p.scionLayer !== p.lastLayer ==>
// @ 	acc(p.lastLayer.Mem(ubLL), R15)
// @ preserves &p.scionLayer === p.lastLayer ==>
// @ 	ub === ubLL
// @ ensures   acc(&p.d, R50) && acc(p.d.Mem(), _)
// @ ensures   acc(p.scionLayer.Mem(ub), R4)
// @ ensures   sl.Bytes(ub, 0, len(ub))
// @ ensures   acc(&p.ingressID,  R45)
// @ ensures   p.d.validResult(respr, false)
// @ ensures   acc(&p.buffer, R50) && p.buffer != nil && p.buffer.Mem()
// @ ensures   sl.Bytes(p.buffer.UBuf(), 0, len(p.buffer.UBuf()))
// @ ensures   respr !== processResult{} ==>
// @ 	respr.OutPkt === p.buffer.UBuf()
// @ ensures   reserr != nil && reserr.ErrorMem()
// @ ensures   respr.OutPkt != nil ==>
// @ 	!slayers.IsSupportedPkt(respr.OutPkt)
// @ decreases
func (p *slowPathPacketProcessor) packSCMP(
	typ slayers.SCMPType,
	code slayers.SCMPCode,
	scmpP gopacket.SerializableLayer,
	isError bool,
	// @ ghost ub []byte,
	// @ ghost ubLL []byte,
	// @ ghost startLL int,
	// @ ghost endLL int,
) error {
	// @ ghost llIsScmp := false
	// @ ghost scmpPldIsNil := false
	// @ ghost maybeStartPld := 0
	// @ ghost maybeEndPld := 0

	// check invoking packet was an SCMP error:
	if p.lastLayer.NextLayerType( /*@ ubLL @*/ ) == slayers.LayerTypeSCMP {
		// @ llIsScmp = true
		var scmpLayer /*@@@*/ slayers.SCMP
		// @ fold scmpLayer.NonInitMem()
		pld /*@ , start, end @*/ := p.lastLayer.LayerPayload( /*@ ubLL @*/ )
		// @ sl.SplitRange_Bytes(ub, startLL, endLL, writePerm)
		// @ maybeStartPld = start
		// @ maybeEndPld = end
		// @ if pld == nil {
		// @ 	scmpPldIsNil = true
		// @ 	fold sl.Bytes(nil, 0, 0)
		// @ } else {
		// @ 	sl.SplitRange_Bytes(ubLL, start, end, writePerm)
		// @ }
		// @ gopacket.AssertInvariantNilDecodeFeedback()
		err := scmpLayer.DecodeFromBytes(pld, gopacket.NilDecodeFeedback)
		if err != nil {
			return serrors.Wrap("decoding SCMP layer", err)
		}
		if !scmpLayer.TypeCode.InfoMsg() {
			return serrors.New("SCMP error for SCMP error pkt -> DROP")
		}
	}

	rawSCMP, err := p.prepareSCMP(typ, code, scmpP, isError)
	if rawSCMP != nil {
		p.pkt.rawPacket = p.pkt.rawPacket[:len(rawSCMP)]
		copy(p.pkt.rawPacket, rawSCMP)
	}

	// We're about to send a packet that has little to do with the one we received.
	// The original traffic type, if one had been set, no-longer applies.
	p.pkt.trafficType = ttOther
	p.pkt.egress = p.pkt.ingress
	updateNetAddrFromNetAddr(p.pkt.dstAddr, p.pkt.srcAddr)
	return err
}

// @ requires  acc(sl.Bytes(ub, 0, len(ub)), R1)
// @ requires  acc(&p.d, R50) && acc(p.d.Mem(), _)
// @ requires  acc(p.scionLayer.Mem(ub), R5)
// @ requires  acc(&p.path, R20)
// @ requires  p.path === p.scionLayer.GetPath(ub)
// @ requires  acc(&p.hopField) && acc(&p.infoField)
// Preconditions for IO:
// @ requires  p.scionLayer.EqAbsHeader(ub)
// @ requires  p.scionLayer.ValidScionInitSpec(ub)
// @ ensures   acc(sl.Bytes(ub, 0, len(ub)), R1)
// @ ensures   acc(&p.d, R50)
// @ ensures   acc(p.scionLayer.Mem(ub), R5)
// @ ensures   acc(&p.path, R20)
// @ ensures   p.path === p.scionLayer.GetPath(ub)
// @ ensures   acc(&p.hopField) && acc(&p.infoField)
// @ ensures   respr === processResult{}
// @ ensures   reserr == nil ==>
// @ 	let ubPath := p.scionLayer.UBPath(ub) in
// @ 	unfolding acc(p.scionLayer.Mem(ub), R10) in
// @ 	p.path.GetBase(ubPath).Valid()
// @ ensures   p.d.validResult(respr, false)
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// Postconditions for IO:
// @ ensures   reserr == nil ==>
// @ 	slayers.ValidPktMetaHdr(ub)  &&
// @ 	p.scionLayer.EqAbsHeader(ub) &&
// @ 	p.scionLayer.ValidPathMetaData(ub)
// @ ensures   reserr == nil ==> absPkt(ub).PathNotFullyTraversed()
// @ ensures   reserr == nil ==> p.EqAbsHopField(absPkt(ub))
// @ ensures   reserr == nil ==> p.EqAbsInfoField(absPkt(ub))
// @ ensures   old(slayers.IsSupportedPkt(ub)) == slayers.IsSupportedPkt(ub)
// @ ensures   respr.OutPkt == nil
// @ decreases
func (p *scionPacketProcessor) parsePath() disposition {
	var err error
	// @ unfold acc(p.scionLayer.Mem(ub), R6)
	// @ defer fold acc(p.scionLayer.Mem(ub), R6)
	// @ ghost startP := p.scionLayer.PathStartIdx(ub)
	// @ ghost endP := p.scionLayer.PathEndIdx(ub)
	// @ ghost ubPath := ub[startP:endP]
	// @ sl.SplitRange_Bytes(ub, startP, endP, R2)
	// @ ghost defer sl.CombineRange_Bytes(ub, startP, endP, R2)
	// (VerifiedSCION) Due to an incompleteness (https://github.com/viperproject/gobra/issues/770),
	// we introduce a temporary variable to be able to call `path.AbsMacArrayCongruence()`.
	var tmpHopField path.HopField
	tmpHopField, err = p.path.GetCurrentHopField( /*@ ubPath @*/ )
	p.hopField = tmpHopField
	// @ path.AbsMacArrayCongruence(p.hopField.Mac, tmpHopField.Mac)
	// @ assert p.hopField.ToIO_HF() == tmpHopField.ToIO_HF()
	// @ assert err == nil ==> reveal p.path.CorrectlyDecodedHf(ubPath, tmpHopField)
	// @ assert err == nil ==> reveal p.path.CorrectlyDecodedHf(ubPath, p.hopField)
	// @ fold p.d.validResult(processResult{}, false)
	if err != nil {
		// TODO(lukedirtwalker) parameter problem invalid path?
		return errorDiscard("error", err)
	}
	p.infoField, err = p.path.GetCurrentInfoField( /*@ ubPath @*/ )
	if err != nil {
		// TODO(lukedirtwalker) parameter problem invalid path?
		return errorDiscard("error", err)
	}
	// Segments without the Peering flag must consist of at least two HFs:
	// https://github.com/scionproto/scion/issues/4524
	// (VerifiedSCION) The version verified here is prior to the support of peering
	// links, so we do not check the Peering flag here.
	hasSingletonSegment :=
		// @ unfolding acc(p.path.Mem(ubPath), _) in
		// @ unfolding acc(p.path.Base.Mem(), _) in
		p.path.PathMeta.SegLen[0] == 1 ||
		p.path.PathMeta.SegLen[1] == 1 ||
		p.path.PathMeta.SegLen[2] == 1

	if !p.infoField.Peer && hasSingletonSegment {
		// @ establishMemMalformedPath()
		return errorDiscard("error", malformedPath)
	}
	if !p.path.CurrINFMatchesCurrHF() {
		// @ establishMemMalformedPath()
		return errorDiscard("error", malformedPath)
	}
	// @ p.EstablishEqAbsHeader(ub, startP, endP)
	// @ p.path.EstablishValidPktMetaHdr(ubPath)
	// @ p.SubSliceAbsPktToAbsPkt(ub, startP, endP)
	// @ absPktFutureLemma(ub)
	// @ p.path.DecodingLemma(ubPath, p.infoField, p.hopField)
	// @ assert reveal p.path.EqAbsInfoField(p.path.absPkt(ubPath),
	// @ 	p.infoField.ToAbsInfoField())
	// @ assert reveal p.path.EqAbsHopField(p.path.absPkt(ubPath),
	// @ 	p.hopField.ToIO_HF())
	// @ assert reveal p.EqAbsHopField(absPkt(ub))
	// @ assert reveal p.EqAbsInfoField(absPkt(ub))
	// @ assert old(reveal slayers.IsSupportedPkt(ub)) == reveal slayers.IsSupportedPkt(ub)
	return pForward
}

func determinePeer(pathMeta scion.MetaHdr, inf path.InfoField) (bool, error) {
	if !inf.Peer {
		return false, nil
	}

	if pathMeta.SegLen[0] == 0 {
		return false, errPeeringEmptySeg0
	}
	if pathMeta.SegLen[1] == 0 {
		return false, errPeeringEmptySeg1

	}
	if pathMeta.SegLen[2] != 0 {
		return false, errPeeringNonemptySeg2
	}

	// The peer hop fields are the last hop field on the first path
	// segment (at SegLen[0] - 1) and the first hop field of the second
	// path segment (at SegLen[0]). The below check applies only
	// because we already know this is a well-formed peering path.
	currHF := pathMeta.CurrHF
	segLen := pathMeta.SegLen[0]
	return currHF == segLen-1 || currHF == segLen, nil
}

func (p *scionPacketProcessor) determinePeer() disposition {
	peer, err := determinePeer(p.path.PathMeta, p.infoField)
	p.peering = peer
	if err != nil {
		return errorDiscard("error", err)
	}
	return pForward
}

// @ requires  0 <= startLL && startLL <= endLL && endLL <= len(ubScionL)
// @ requires  acc(&p.path, R20)
// @ requires  sl.Bytes(ubScionL, 0, len(ubScionL))
// @ requires  acc(p.scionLayer.Mem(ubScionL), R3)
// @ requires  p.scionLayer.ValidPathMetaData(ubScionL)
// @ requires  acc(&p.d, R50) && acc(p.d.Mem(), _)
// @ requires  p.path == p.scionLayer.GetPath(ubScionL)
// @ requires  acc(&p.buffer, R50) && p.buffer != nil && p.buffer.Mem()
// @ requires  sl.Bytes(p.buffer.UBuf(), 0, len(p.buffer.UBuf()))
// pres for IO:
// @ requires  slayers.ValidPktMetaHdr(ubScionL) && p.scionLayer.EqAbsHeader(ubScionL)
// @ requires  absPkt(ubScionL).PathNotFullyTraversed()
// @ preserves ubLL == nil || ubLL === ubScionL[startLL:endLL]
// @ preserves acc(&p.lastLayer, R55) && p.lastLayer != nil
// @ preserves &p.scionLayer !== p.lastLayer ==>
// @ 	acc(p.lastLayer.Mem(ubLL), R15)
// @ preserves &p.scionLayer === p.lastLayer ==>
// @ 	ubScionL === ubLL
// @ preserves acc(&p.infoField, R20)
// @ preserves acc(&p.hopField, R20)
// @ preserves acc(&p.ingressID, R20)
// @ ensures   acc(&p.path, R20)
// @ ensures   acc(&p.d, R50) && acc(p.d.Mem(), _)
// @ ensures   acc(p.scionLayer.Mem(ubScionL), R3)
// @ ensures   sl.Bytes(ubScionL, 0, len(ubScionL))
// @ ensures   p.d.validResult(respr, false)
// @ ensures   acc(&p.buffer, R50) && p.buffer != nil && p.buffer.Mem()
// @ ensures   sl.Bytes(p.buffer.UBuf(), 0, len(p.buffer.UBuf()))
// @ ensures   respr !== processResult{} ==>
// @ 	respr.OutPkt === p.buffer.UBuf()
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// @ ensures   reserr == nil ==>
// @ 	respr === processResult{}
// posts for IO:
// @ ensures   reserr == nil ==> slayers.ValidPktMetaHdr(ubScionL) && p.scionLayer.EqAbsHeader(ubScionL)
// @ ensures   reserr == nil ==> absPkt(ubScionL).PathNotFullyTraversed()
// @ ensures   reserr == nil ==> absPkt(ubScionL) == old(absPkt(ubScionL))
// @ ensures   reserr == nil ==> old(slayers.IsSupportedPkt(ubScionL)) == slayers.IsSupportedPkt(ubScionL)
// @ ensures   reserr != nil && respr.OutPkt != nil ==>
// @ 	absIO_val(respr.OutPkt, respr.EgressID).isIO_val_Unsupported
// @ decreases
func (p *scionPacketProcessor) validateHopExpiry( /*@ ghost ubScionL []byte, ghost ubLL []byte, ghost startLL int, ghost endLL int @*/ ) disposition {
	expiration := util.SecsToTime(p.infoField.Timestamp).
		Add(path.ExpTimeToDuration(p.hopField.ExpTime))
	expired := expiration.Before(time.Now())
	if !expired {
		// @ fold p.d.validResult(respr, false)
		pktIngressID := p.hopField.ConsIngress
		return pForward
	}
	log.Debug("SCMP response", "cause", expiredHop,
		"cons_dir", p.infoField.ConsDir, "if_id", p.pkt.ingress,
		"curr_inf", p.path.PathMeta.CurrINF, "curr_hf", p.path.PathMeta.CurrHF)
	p.pkt.slowPathRequest = slowPathRequest{
		scmpType: slayers.SCMPTypeParameterProblem,
		code:     slayers.SCMPCodePathExpired,
		pointer:  p.currentHopPointer(),
	}
	return pSlowPath
}

// @ requires  0 <= startLL && startLL <= endLL && endLL <= len(ubScionL)
// @ requires  acc(&p.path, R20)
// @ requires  sl.Bytes(ubScionL, 0, len(ubScionL))
// @ requires  acc(p.scionLayer.Mem(ubScionL), R3)
// @ requires  p.scionLayer.ValidPathMetaData(ubScionL)
// @ requires  p.path == p.scionLayer.GetPath(ubScionL)
// @ requires  acc(&p.buffer, R50) && p.buffer != nil && p.buffer.Mem()
// @ requires  sl.Bytes(p.buffer.UBuf(), 0, len(p.buffer.UBuf()))
// @ requires  acc(&p.ingressID, R21)
// @ requires  acc(&p.hopField, R20)
// @ requires  acc(&p.infoField, R20)
// @ requires  acc(&p.d, R50) && acc(p.d.Mem(), _)
// @ preserves ubLL == nil || ubLL === ubScionL[startLL:endLL]
// @ preserves  acc(&p.lastLayer, R55) && p.lastLayer != nil
// @ preserves  &p.scionLayer !== p.lastLayer ==>
// @ 	acc(p.lastLayer.Mem(ubLL), R15)
// @ preserves  &p.scionLayer === p.lastLayer ==>
// @ 	ubScionL === ubLL
// @ ensures   acc(&p.d, R50)
// @ ensures   acc(&p.path, R20)
// @ ensures   acc(&p.infoField, R20)
// @ ensures   acc(&p.hopField, R20)
// @ ensures   acc(&p.ingressID, R21)
// @ ensures   reserr == nil && p.infoField.ConsDir ==> (
// @ 	p.ingressID == 0 || p.hopField.ConsIngress == p.ingressID)
// @ ensures   reserr == nil && !p.infoField.ConsDir ==> (
// @ 	p.ingressID == 0 || p.hopField.ConsEgress == p.ingressID)
// @ ensures   acc(p.scionLayer.Mem(ubScionL), R3)
// @ ensures   sl.Bytes(ubScionL, 0, len(ubScionL))
// @ ensures   p.d.validResult(respr, false)
// @ ensures   acc(&p.buffer, R50) && p.buffer != nil && p.buffer.Mem()
// @ ensures   sl.Bytes(p.buffer.UBuf(), 0, len(p.buffer.UBuf()))
// @ ensures   respr !== processResult{} ==>
// @ 	respr.OutPkt === p.buffer.UBuf()
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// @ ensures   reserr == nil ==>
// @ 	respr === processResult{}
// contracts for IO-spec
// @ requires  slayers.ValidPktMetaHdr(ubScionL) && p.scionLayer.EqAbsHeader(ubScionL)
// @ requires  absPkt(ubScionL).PathNotFullyTraversed()
// @ requires  p.EqAbsHopField(absPkt(ubScionL))
// @ requires  p.EqAbsInfoField(absPkt(ubScionL))
// @ ensures   reserr == nil ==> slayers.ValidPktMetaHdr(ubScionL) && p.scionLayer.EqAbsHeader(ubScionL)
// @ ensures   reserr == nil ==> absPkt(ubScionL) == old(absPkt(ubScionL))
// @ ensures   reserr == nil ==> old(slayers.IsSupportedPkt(ubScionL)) == slayers.IsSupportedPkt(ubScionL)
// @ ensures   reserr == nil ==>
// @ 	AbsValidateIngressIDConstraint(absPkt(ubScionL), path.ifsToIO_ifs(p.ingressID))
// @ ensures   reserr != nil && respr.OutPkt != nil ==>
// @ 	absIO_val(respr.OutPkt, respr.EgressID).isIO_val_Unsupported
// @ decreases
func (p *scionPacketProcessor) validateIngressID( /*@ ghost ubScionL []byte, ghost ubLL []byte, ghost startLL int, ghost endLL int@*/ ) disposition {
	hdrIngressID := p.hopField.ConsIngress
	errCode := slayers.SCMPCodeUnknownHopFieldIngress
	if !p.infoField.ConsDir {
		hdrIngressID = p.hopField.ConsEgress
		errCode = slayers.SCMPCodeUnknownHopFieldEgress
	}
	if p.pkt.ingress != 0 && p.pkt.ingress != hdrIngressID {
		log.Debug("SCMP response", "cause", ingressInterfaceInvalid,
			"pkt_ingress", hdrIngressID, "router_ingress", p.pkt.ingress)
		p.pkt.slowPathRequest = slowPathRequest{
			scmpType: slayers.SCMPTypeParameterProblem,
			code:     errCode,
			pointer:  p.currentHopPointer(),
		}
		// @ ghost if tmpErr != nil && tmpRes.OutPkt != nil {
		// @ 	AbsUnsupportedPktIsUnsupportedVal(tmpRes.OutPkt, tmpRes.EgressID)
		// @ }
		return pSlowPath
	}
	// @ ghost oldPkt := absPkt(ubScionL)
	// @ reveal p.EqAbsHopField(oldPkt)
	// @ reveal p.EqAbsInfoField(oldPkt)
	// @ assert reveal AbsValidateIngressIDConstraint(oldPkt, path.ifsToIO_ifs(p.ingressID))
	// @ fold p.d.validResult(respr, false)
	return pForward
}

// @ requires  0 <= startLL && startLL <= endLL && endLL <= len(ubScionL)
// @ requires  acc(&p.path, R20)
// @ requires  sl.Bytes(ubScionL, 0, len(ubScionL))
// @ requires  acc(p.scionLayer.Mem(ubScionL), R2)
// @ requires  p.scionLayer.ValidPathMetaData(ubScionL)
// @ requires  p.path == p.scionLayer.GetPath(ubScionL)
// @ requires  acc(&p.buffer, R50) && p.buffer != nil && p.buffer.Mem()
// @ requires  sl.Bytes(p.buffer.UBuf(), 0, len(p.buffer.UBuf()))
// @ requires  acc(&p.d, R50) && acc(p.d.Mem(), _)
// @ preserves acc(&p.ingressID, R21)
// @ preserves ubLL == nil || ubLL === ubScionL[startLL:endLL]
// @ preserves acc(&p.lastLayer, R55) && p.lastLayer != nil
// @ preserves &p.scionLayer !== p.lastLayer ==>
// @ 	acc(p.lastLayer.Mem(ubLL), R15)
// @ preserves &p.scionLayer === p.lastLayer ==>
// @ 	ubScionL === ubLL
// @ ensures   acc(p.scionLayer.Mem(ubScionL), R2)
// @ ensures   acc(&p.path, R20)
// @ ensures   acc(&p.d, R50) && acc(p.d.Mem(), _)
// @ ensures   sl.Bytes(ubScionL, 0, len(ubScionL))
// @ ensures   p.d.validResult(respr, false)
// @ ensures   acc(&p.buffer, R50) && p.buffer != nil && p.buffer.Mem()
// @ ensures   sl.Bytes(p.buffer.UBuf(), 0, len(p.buffer.UBuf()))
// @ ensures   respr !== processResult{} ==>
// @ 	respr.OutPkt === p.buffer.UBuf()
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// @ ensures   reserr == nil ==>
// @ 	respr === processResult{}
// contracts for IO-spec
// @ requires  slayers.ValidPktMetaHdr(ubScionL) && p.scionLayer.EqAbsHeader(ubScionL)
// @ requires  absPkt(ubScionL).PathNotFullyTraversed()
// @ ensures   reserr == nil ==> slayers.ValidPktMetaHdr(ubScionL) && p.scionLayer.EqAbsHeader(ubScionL)
// @ ensures   reserr == nil ==> p.DstIsLocalIngressID(ubScionL)
// @ ensures   reserr == nil ==> p.LastHopLen(ubScionL)
// @ ensures   reserr == nil ==> absPkt(ubScionL).PathNotFullyTraversed()
// @ ensures   reserr == nil ==> absPkt(ubScionL) == old(absPkt(ubScionL))
// @ ensures   reserr == nil ==> old(slayers.IsSupportedPkt(ubScionL)) == slayers.IsSupportedPkt(ubScionL)
// @ ensures   reserr != nil && respr.OutPkt != nil ==>
// @ 	absIO_val(respr.OutPkt, respr.EgressID).isIO_val_Unsupported
// @ decreases
func (p *scionPacketProcessor) validateSrcDstIA( /*@ ghost ubScionL []byte, ghost ubLL []byte, ghost startLL int, ghost endLL int @*/ ) disposition {
	// @ unfold acc(p.scionLayer.Mem(ubScionL), R20)
	// @ defer fold acc(p.scionLayer.Mem(ubScionL), R20)
	// @ ghost startP := p.scionLayer.PathStartIdx(ubScionL)
	// @ ghost endP := p.scionLayer.PathEndIdx(ubScionL)
	// @ ghost ubPath := ubScionL[startP:endP]
	// @ sl.SplitRange_Bytes(ubScionL, startP, endP, R50)
	// @ p.AbsPktToSubSliceAbsPkt(ubScionL, startP, endP)
	// @ p.scionLayer.ValidHeaderOffsetToSubSliceLemma(ubScionL, startP)
	// @ unfold acc(p.scionLayer.HeaderMem(ubScionL[slayers.CmnHdrLen:]), R20)
	// @ defer fold acc(p.scionLayer.HeaderMem(ubScionL[slayers.CmnHdrLen:]), R20)
	// @ p.d.getLocalIA()
	srcIsLocal := (p.scionLayer.SrcIA == p.d.localIA)
	dstIsLocal := (p.scionLayer.DstIA == p.d.localIA)
	if p.pkt.ingress == 0 {
		// Outbound
		// Only check SrcIA if first hop, for transit this already checked by ingress router.
		// Note: SCMP error messages triggered by the sibling router may use paths that
		// don't start with the first hop.
		if p.path.IsFirstHop( /*@ ubPath @*/ ) && !srcIsLocal {
			return p.respInvalidSrcIA()
		}
		if dstIsLocal {
			return p.respInvalidDstIA()
		}
	} else {
		// Inbound
		if srcIsLocal {
			return p.respInvalidSrcIA()
		}
		if p.path.IsLastHop() != dstIsLocal {
			return p.respInvalidDstIA()
		}
		// @ ghost if(p.path.IsLastHopSpec(ubPath)) {
		// @ 	p.path.LastHopLemma(ubPath)
		// @ 	p.scionLayer.ValidHeaderOffsetFromSubSliceLemma(ubScionL, startP)
		// @ 	p.SubSliceAbsPktToAbsPkt(ubScionL, startP, endP)
		// @ }
	}
	// @ fold p.d.validResult(processResult{}, false)
	// @ assert  (unfolding acc(p.scionLayer.Mem(ubScionL), R55) in
	// @ 	(unfolding acc(p.scionLayer.HeaderMem(ubScionL[slayers.CmnHdrLen:]), R55) in
	// @ 	p.scionLayer.DstIA) == (unfolding acc(p.d.Mem(), _) in p.d.localIA)) ==> p.ingressID != 0
	// @ assert  (unfolding acc(p.scionLayer.Mem(ubScionL), R55) in
	// @ 	(unfolding acc(p.scionLayer.HeaderMem(ubScionL[slayers.CmnHdrLen:]), R55) in
	// @ 	p.scionLayer.DstIA) == (unfolding acc(p.d.Mem(), _) in p.d.localIA)) ==> p.path.IsLastHopSpec(ubPath)
	// @ assert reveal p.DstIsLocalIngressID(ubScionL)
	// @ assert reveal p.LastHopLen(ubScionL)
	// @ ghost sl.CombineRange_Bytes(ubScionL, startP, endP, R50)
	return pForward
}

// invalidSrcIA is a helper to return an SCMP error for an invalid SrcIA.
// @ requires  0 <= startLL && startLL <= endLL && endLL <= len(ub)
// @ requires  acc(&p.path, R20)
// @ requires  sl.Bytes(ub, 0, len(ub))
// @ requires  acc(p.scionLayer.Mem(ub), R3)
// @ requires  p.scionLayer.ValidPathMetaData(ub)
// @ requires  p.path == p.scionLayer.GetPath(ub)
// @ requires  acc(&p.buffer, R50) && p.buffer != nil && p.buffer.Mem()
// @ requires  sl.Bytes(p.buffer.UBuf(), 0, len(p.buffer.UBuf()))
// @ requires  acc(&p.d, R50) && acc(p.d.Mem(), _)
// @ preserves acc(&p.ingressID, R40)
// @ preserves ubLL == nil || ubLL === ub[startLL:endLL]
// @ preserves acc(&p.lastLayer, R55) && p.lastLayer != nil
// @ preserves &p.scionLayer !== p.lastLayer ==>
// @ 	acc(p.lastLayer.Mem(ubLL), R15)
// @ preserves &p.scionLayer === p.lastLayer ==>
// @ 	ub === ubLL
// @ ensures   acc(&p.d, R50) && acc(p.d.Mem(), _)
// @ ensures   acc(&p.path, R20)
// @ ensures   acc(p.scionLayer.Mem(ub), R3)
// @ ensures   sl.Bytes(ub, 0, len(ub))
// @ ensures   p.d.validResult(respr, false)
// @ ensures   acc(&p.buffer, R50) && p.buffer != nil && p.buffer.Mem()
// @ ensures   sl.Bytes(p.buffer.UBuf(), 0, len(p.buffer.UBuf()))
// @ ensures   respr !== processResult{} ==>
// @ 	respr.OutPkt === p.buffer.UBuf()
// @ ensures   reserr != nil && reserr.ErrorMem()
// @ ensures   respr.OutPkt != nil ==>
// @ 	absIO_val(respr.OutPkt, respr.EgressID).isIO_val_Unsupported
// @ decreases
func (p *scionPacketProcessor) respInvalidSrcIA() disposition {
	log.Debug("SCMP response", "cause", invalidSrcIA)
	p.pkt.slowPathRequest = slowPathRequest{
		scmpType: slayers.SCMPTypeParameterProblem,
		code:     slayers.SCMPCodeInvalidSourceAddress,
		pointer:  uint16(slayers.CmnHdrLen + addr.IABytes),
	}
	return pSlowPath
}

// invalidDstIA is a helper to return an SCMP error for an invalid DstIA.
// @ requires  0 <= startLL && startLL <= endLL && endLL <= len(ub)
// @ requires  acc(&p.path, R20)
// @ requires  sl.Bytes(ub, 0, len(ub))
// @ requires  acc(p.scionLayer.Mem(ub), R3)
// @ requires  p.scionLayer.ValidPathMetaData(ub)
// @ requires  p.path == p.scionLayer.GetPath(ub)
// @ requires  acc(&p.buffer, R50) && p.buffer != nil && p.buffer.Mem()
// @ requires  sl.Bytes(p.buffer.UBuf(), 0, len(p.buffer.UBuf()))
// @ requires  acc(&p.d, R50) && acc(p.d.Mem(), _)
// @ preserves acc(&p.ingressID, R40)
// @ preserves ubLL == nil || ubLL === ub[startLL:endLL]
// @ preserves acc(&p.lastLayer, R55) && p.lastLayer != nil
// @ preserves &p.scionLayer !== p.lastLayer ==>
// @ 	acc(p.lastLayer.Mem(ubLL), R15)
// @ preserves &p.scionLayer === p.lastLayer ==>
// @ 	ub === ubLL
// @ ensures   acc(&p.d, R50) && acc(p.d.Mem(), _)
// @ ensures   acc(&p.path, R20)
// @ ensures   acc(p.scionLayer.Mem(ub), R3)
// @ ensures   sl.Bytes(ub, 0, len(ub))
// @ ensures   p.d.validResult(respr, false)
// @ ensures   acc(&p.buffer, R50) && p.buffer != nil && p.buffer.Mem()
// @ ensures   sl.Bytes(p.buffer.UBuf(), 0, len(p.buffer.UBuf()))
// @ ensures   respr !== processResult{} ==>
// @ 	respr.OutPkt === p.buffer.UBuf()
// @ ensures   reserr != nil && reserr.ErrorMem()
// @ ensures   respr.OutPkt != nil ==>
// @ 	absIO_val(respr.OutPkt, respr.EgressID).isIO_val_Unsupported
// @ decreases
func (p *scionPacketProcessor) respInvalidDstIA() disposition {
	log.Debug("SCMP response", "cause", invalidDstIA)
	p.pkt.slowPathRequest = slowPathRequest{
		scmpType: slayers.SCMPTypeParameterProblem,
		code:     slayers.SCMPCodeInvalidDestinationAddress,
		pointer:  uint16(slayers.CmnHdrLen),
	}
	return pSlowPath
}

// validateTransitUnderlaySrc checks that the source address of transit packets
// matches the expected sibling router.
// Provided that underlying network infrastructure prevents address spoofing,
// this check prevents malicious end hosts in the local AS from bypassing the
// SrcIA checks by disguising packets as transit traffic.
// @ requires  acc(&p.path, R15)
// @ requires  acc(p.scionLayer.Mem(ub), R4)
// @ requires  p.path === p.scionLayer.GetPath(ub)
// @ requires  acc(&p.ingressID, R21)
// @ requires  acc(&p.infoField, R4) && acc(&p.hopField, R4)
// @ requires  let ubPath := p.scionLayer.UBPath(ub) in
// @ 	unfolding acc(p.scionLayer.Mem(ub), R10) in
// @ 	p.path.GetCurrHF(ubPath) <= p.path.GetNumHops(ubPath)
// @ requires  let ubPath := p.scionLayer.UBPath(ub) in
// @ 	unfolding acc(p.scionLayer.Mem(ub), R10) in
// @ 	p.path.GetCurrINF(ubPath) <= p.path.GetNumINF(ubPath)
// @ requires  acc(&p.d, R20) && acc(p.d.Mem(), _)
// @ requires  acc(&p.srcAddr, R20) && acc(p.srcAddr.Mem(), _)
// @ preserves acc(sl.Bytes(ub, 0, len(ub)), R4)
// @ ensures   acc(&p.path, R15)
// @ ensures   acc(p.scionLayer.Mem(ub), R4)
// @ ensures   acc(&p.ingressID, R21)
// @ ensures   acc(&p.infoField, R4) && acc(&p.hopField, R4)
// @ ensures   acc(&p.d, R20)
// @ ensures   acc(&p.srcAddr, R20)
// @ ensures   p.d.validResult(respr, false)
// @ ensures   respr.OutPkt == nil
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// @ ensures   respr === processResult{}
// @ decreases
func (p *scionPacketProcessor) validateTransitUnderlaySrc( /*@ ghost ub []byte @*/ ) disposition {
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
	if p.path.IsFirstHop( /*@ ubPath @*/ ) || p.pkt.ingress != 0 {
		// not a transit packet, nothing to check
		// @ fold p.d.validResult(processResult{}, false)
		return pForward
	}
	pktIngressID := p.ingressInterface(( /*@ ubPath @*/ )
	// @ p.d.getInternalNextHops()
	// @ ghost if p.d.internalNextHops != nil { unfold acc(accAddr(p.d.internalNextHops), _) }
	expectedSrc, okE := p.d.internalNextHops[pktIngressID]
	// @ ghost if ok {
	// @ 	assert expectedSrc in range(p.d.internalNextHops)
	// @    unfold acc(expectedSrc.Mem(), _)
	// @ }
	// @ unfold acc(p.srcAddr.Mem(), _)
	if !okE {
		// Drop
		// @ establishInvalidSrcAddrForTransit()
		// @ fold p.d.validResult(processResult{}, false)
		return errorDiscard("error", invalidSrcAddrForTransit)
	}
	src, okS := netip.AddrFromSlice(p.pkt.srcAddr.IP)
	if !(okS && expectedSrc.Addr() == src) {
		// Drop
		return errorDiscard("error", invalidSrcAddrForTransit)
	}
	// @ fold p.d.validResult(processResult{}, false)
	return pForward
}

// Validates the egress interface referenced by the current hop.
// @ requires  0 <= startLL && startLL <= endLL && endLL <= len(ubScionL)
// @ requires  acc(&p.path, R20)
// @ requires  sl.Bytes(ubScionL, 0, len(ubScionL))
// @ requires  acc(p.scionLayer.Mem(ubScionL), R3)
// @ requires  p.scionLayer.ValidPathMetaData(ubScionL)
// @ requires  acc(&p.d, R50) && acc(p.d.Mem(), _)
// @ requires  p.path == p.scionLayer.GetPath(ubScionL)
// @ requires  acc(&p.buffer, R50) && p.buffer != nil && p.buffer.Mem()
// @ requires   sl.Bytes(p.buffer.UBuf(), 0, len(p.buffer.UBuf()))
// @ requires  acc(&p.segmentChange, R20)
// @ requires  acc(&p.ingressID, R21)
// @ requires  acc(&p.infoField, R20)
// @ requires  acc(&p.hopField, R20)
// @ preserves ubLL == nil || ubLL === ubScionL[startLL:endLL]
// @ preserves acc(&p.lastLayer, R55) && p.lastLayer != nil
// @ preserves &p.scionLayer !== p.lastLayer ==>
// @ 	acc(p.lastLayer.Mem(ubLL), R15)
// @ preserves &p.scionLayer === p.lastLayer ==>
// @ 	ubScionL === ubLL
// @ ensures   acc(&p.infoField, R20)
// @ ensures   acc(&p.hopField, R20)
// @ ensures   acc(&p.ingressID, R21)
// @ ensures   acc(&p.segmentChange, R20)
// @ ensures   acc(&p.path, R20)
// @ ensures   acc(&p.d, R50) && acc(p.d.Mem(), _)
// @ ensures   acc(p.scionLayer.Mem(ubScionL), R3)
// @ ensures   sl.Bytes(ubScionL, 0, len(ubScionL))
// @ ensures   p.d.validResult(respr, false)
// @ ensures   acc(&p.buffer, R50) && p.buffer != nil && p.buffer.Mem()
// @ ensures   sl.Bytes(p.buffer.UBuf(), 0, len(p.buffer.UBuf()))
// @ ensures   respr !== processResult{} ==>
// @ 	respr.OutPkt === p.buffer.UBuf()
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// @ ensures   reserr == nil ==>
// @ 	respr === processResult{}
// contracts for IO-spec
// @ requires  dp.Valid()
// @ requires  p.d.WellConfigured()
// @ requires  p.d.DpAgreesWithSpec(dp)
// @ requires  slayers.ValidPktMetaHdr(ubScionL) && p.scionLayer.EqAbsHeader(ubScionL)
// @ requires  absPkt(ubScionL).PathNotFullyTraversed()
// @ requires  p.EqAbsHopField(absPkt(ubScionL))
// @ requires  p.EqAbsInfoField(absPkt(ubScionL))
// @ requires  p.segmentChange ==>
// @ 	absPkt(ubScionL).RightSeg != none[io.IO_seg2] && len(get(absPkt(ubScionL).RightSeg).Past) > 0
// @ requires  !p.segmentChange ==>
// @ 	AbsValidateIngressIDConstraint(absPkt(ubScionL), path.ifsToIO_ifs(p.ingressID))
// @ requires  p.segmentChange ==>
// @ 	AbsValidateIngressIDConstraintXover(absPkt(ubScionL), path.ifsToIO_ifs(p.ingressID))
// @ ensures   reserr == nil ==> slayers.ValidPktMetaHdr(ubScionL) && p.scionLayer.EqAbsHeader(ubScionL)
// @ ensures   reserr == nil ==> absPkt(ubScionL) == old(absPkt(ubScionL))
// @ ensures   reserr == nil ==> old(slayers.IsSupportedPkt(ubScionL)) == slayers.IsSupportedPkt(ubScionL)
// @ ensures   reserr == nil ==> p.NoBouncingPkt(absPkt(ubScionL))
// @ ensures   reserr == nil && !p.segmentChange ==>
// @ 	AbsValidateEgressIDConstraint(absPkt(ubScionL), (p.ingressID != 0), dp)
// @ ensures   reserr == nil && p.segmentChange ==>
// @ 	absPkt(ubScionL).RightSeg != none[io.IO_seg2] && len(get(absPkt(ubScionL).RightSeg).Past) > 0
// @ ensures   reserr == nil && p.segmentChange ==>
// @ 	p.ingressID != 0 && AbsValidateEgressIDConstraintXover(absPkt(ubScionL), dp)
// @ ensures   reserr != nil && respr.OutPkt != nil ==>
// @ 	absIO_val(respr.OutPkt, respr.EgressID).isIO_val_Unsupported
// @ decreases
func (p *scionPacketProcessor) validateEgressID( /*@ ghost dp io.DataPlaneSpec, ghost ubScionL []byte, ghost ubLL []byte, ghost startLL int, ghost endLL int @*/ ) disposition {
	// @ ghost oldPkt := absPkt(ubScionL)
	egressID := p.pkt.egress
	// @ reveal AbsEgressInterfaceConstraint(oldPkt, path.ifsToIO_ifs(pktEgressID))
	// @ p.d.getInternalNextHops()
	// @ if p.d.internalNextHops != nil { unfold acc(accAddr(p.d.internalNextHops), _) }
	_, ih := p.d.internalNextHops[egressID]
	// @ p.d.getExternalMem()
	// @ if p.d.external != nil { unfold acc(accBatchConn(p.d.external), _) }
	_, eh := p.d.external[egressID]
	// egress interface must be a known interface
	// packet coming from internal interface, must go to an external interface
	// packet coming from external interface can go to either internal or external interface
	// egress interface must be a known interface
	// packet coming from internal interface, must go to an external interface
	// packet coming from external interface can go to either internal or external interface
	if !ih && !eh || (p.pkt.ingress == 0) && !eh {
		// @ establishCannotRoute()
		errCode := slayers.SCMPCodeUnknownHopFieldEgress
		if !p.infoField.ConsDir {
			errCode = slayers.SCMPCodeUnknownHopFieldIngress
		}
		log.Debug("SCMP response", "cause", cannotRoute)
		p.pkt.slowPathRequest = slowPathRequest{
			scmpType: slayers.SCMPTypeParameterProblem,
			code:     errCode,
			pointer:  p.currentHopPointer(),
		}
		return pSlowPath
	}
	// @ p.d.getDomExternalLemma()
	// @ p.EstablishNoBouncingPkt(oldPkt, pktEgressID)
	// @ p.d.getLinkTypesMem()
	ingressLT, egressLT := p.d.linkTypes[p.pkt.ingress], p.d.linkTypes[egressID]
	// @ p.d.LinkTypesLemma(dp)
	if !p.effectiveXover {
		// Check that the interface pair is valid within a single segment.
		// No check required if the packet is received from an internal interface.
		// This case applies to peering hops as a peering hop isn't an effective
		// cross-over (eventhough it is a segment change).
		// @ assert reveal AbsValidateIngressIDConstraint(oldPkt, path.ifsToIO_ifs(p.ingressID))
		switch {
		case p.pkt.ingress == 0:
			// @ assert reveal AbsValidateEgressIDConstraint(oldPkt, (p.ingressID != 0), dp)
			// @ fold p.d.validResult(respr, false)
			return pForward
		case ingressLT == topology.Core && egressLT == topology.Core:
			// @ assert reveal AbsValidateEgressIDConstraint(oldPkt, (p.ingressID != 0), dp)
			// @ fold p.d.validResult(respr, false)
			return pForward
		case ingressLT == topology.Child && egressLT == topology.Parent:
			// @ assert reveal AbsValidateEgressIDConstraint(oldPkt, (p.ingressID != 0), dp)
			// @ fold p.d.validResult(respr, false)
			return pForward
		case ingressLT == topology.Parent && egressLT == topology.Child:
			// @ assert reveal AbsValidateEgressIDConstraint(oldPkt, (p.ingressID != 0), dp)
			// @ fold p.d.validResult(respr, false)
			return pForward
		case ingressLT == topology.Child && egressLT == topology.Peer:
			return pForward
		case ingressLT == topology.Peer && egressLT == topology.Child:
			return pForward
		default: // malicious
			// @ establishCannotRoute()
			log.Debug("SCMP response", "cause", cannotRoute,
				"ingress_id", p.pkt.ingress, "ingress_type", ingressLT,
				"egress_id", egressID, "egress_type", egressLT)
			p.pkt.slowPathRequest = slowPathRequest{
				scmpType: slayers.SCMPTypeParameterProblem,
				code:     slayers.SCMPCodeInvalidPath, // XXX(matzf) new code InvalidHop?,
				pointer:  p.currentHopPointer(),
			}
			return pSlowPath
		}
	}
	// @ assert reveal AbsValidateIngressIDConstraintXover(oldPkt, path.ifsToIO_ifs(p.ingressID))
	// Check that the interface pair is valid on a segment switch.
	// Having a segment change received from the internal interface is never valid.
	// We should never see a peering link traversal either. If that happens
	// treat it as a routing error (not sure if that can happen without an internal
	// error, though).
	switch {
	case ingressLT == topology.Core && egressLT == topology.Child:
		// @ assert reveal AbsValidateEgressIDConstraintXover(oldPkt, dp)
		// @ fold p.d.validResult(respr, false)
		return pForward
	case ingressLT == topology.Child && egressLT == topology.Core:
		// @ assert reveal AbsValidateEgressIDConstraintXover(oldPkt, dp)
		// @ fold p.d.validResult(respr, false)
		return pForward
	case ingressLT == topology.Child && egressLT == topology.Child:
		// @ assert reveal AbsValidateEgressIDConstraintXover(oldPkt, dp)
		// @ fold p.d.validResult(respr, false)
		return pForward
	default:
		// @ establishCannotRoute()
		log.Debug("SCMP response", "cause", cannotRoute,
			"ingress_id", p.pkt.ingress, "ingress_type", ingressLT,
			"egress_id", egressID, "egress_type", egressLT)
		p.pkt.slowPathRequest = slowPathRequest{
			scmpType: slayers.SCMPTypeParameterProblem,
			code:     slayers.SCMPCodeInvalidSegmentChange,
			pointer:  p.currentInfoPointer(),
		}
		return pSlowPath
	}
}

// @ requires  acc(&p.infoField)
// @ requires  acc(&p.path, R20)
// @ requires  acc(p.scionLayer.Mem(ub), R19)
// @ requires  p.path === p.scionLayer.GetPath(ub)
// @ requires  acc(&p.hopField,  R20)
// @ requires  sl.Bytes(ub, 0, len(ub))
// @ requires  acc(&p.ingressID, R21)
// preconditions for IO:
// @ requires  slayers.ValidPktMetaHdr(ub) && p.scionLayer.EqAbsHeader(ub)
// @ requires  absPkt(ub).PathNotFullyTraversed()
// @ requires  acc(&p.d, R55) && acc(p.d.Mem(), _) && acc(&p.ingressID, R55)
// @ requires  p.LastHopLen(ub)
// @ requires  p.EqAbsHopField(absPkt(ub))
// @ requires  p.EqAbsInfoField(absPkt(ub))
// @ ensures   acc(&p.ingressID, R21)
// @ ensures   acc(&p.hopField,  R20)
// @ ensures   sl.Bytes(ub, 0, len(ub))
// @ ensures   acc(&p.infoField)
// @ ensures   acc(&p.path, R20)
// @ ensures   acc(p.scionLayer.Mem(ub), R19)
// @ ensures   err != nil ==> err.ErrorMem()
// posconditions for IO:
// @ ensures   acc(&p.d, R55) && acc(p.d.Mem(), _) && acc(&p.ingressID, R55)
// @ ensures   err == nil ==> slayers.ValidPktMetaHdr(ub) && p.scionLayer.EqAbsHeader(ub)
// @ ensures   err == nil ==> absPkt(ub).PathNotFullyTraversed()
// @ ensures   err == nil ==>
// @ 	absPkt(ub) == AbsUpdateNonConsDirIngressSegID(old(absPkt(ub)), path.ifsToIO_ifs(p.ingressID))
// @ ensures   err == nil ==> p.LastHopLen(ub)
// @ ensures   err == nil ==> p.EqAbsHopField(absPkt(ub))
// @ ensures   err == nil ==> p.EqAbsInfoField(absPkt(ub))
// @ ensures   err == nil ==> old(slayers.IsSupportedPkt(ub)) == slayers.IsSupportedPkt(ub)
// @ decreases
func (p *scionPacketProcessor) updateNonConsDirIngressSegID( /*@ ghost ub []byte @*/ ) disposition {
	// against construction dir the ingress router updates the SegID, ifID == 0
	// means this comes from this AS itself, so nothing has to be done.
	// For packets destined to peer links this shouldn't be updated.
	// @ ghost ubPath := p.scionLayer.UBPath(ub)
	// @ ghost start := p.scionLayer.PathStartIdx(ub)
	// @ ghost end   := p.scionLayer.PathEndIdx(ub)
	// @ assert ub[start:end] === ubPath

	// @ unfold acc(p.scionLayer.Mem(ub), R20)
	// @ defer fold acc(p.scionLayer.Mem(ub), R20)
	// @ reveal p.EqAbsInfoField(absPkt(ub))
	// @ reveal p.EqAbsHopField(absPkt(ub))
	if !p.infoField.ConsDir && p.pkt.ingress != 0 && !p.peering {
		p.infoField.UpdateSegID(p.hopField.Mac)
		// @ reveal p.LastHopLen(ub)
		// @ assert path.AbsUInfoFromUint16(p.infoField.SegID) ==
		// @ 	old(io.upd_uinfo(path.AbsUInfoFromUint16(p.infoField.SegID), p.hopField.ToIO_HF()))
		// (VerifiedSCION) the following property is guaranteed by the type system, but Gobra cannot infer it yet
		// @ assume 0 <= p.path.GetCurrINF(ubPath)
		// @ sl.SplitRange_Bytes(ub, start, end, HalfPerm)
		// @ sl.SplitByIndex_Bytes(ub, 0, start, slayers.CmnHdrLen, R54)
		// @ sl.Reslice_Bytes(ub, 0, slayers.CmnHdrLen, R54)
		// @ slayers.IsSupportedPktSubslice(ub, slayers.CmnHdrLen)
		// @ p.AbsPktToSubSliceAbsPkt(ub, start, end)
		// @ p.scionLayer.ValidHeaderOffsetToSubSliceLemma(ub, start)
		// @ sl.SplitRange_Bytes(ub, start, end, HalfPerm)
		if err := p.path.SetInfoField(p.infoField, int(p.path.PathMeta.CurrINF)); err != nil {
			// @ sl.Unslice_Bytes(ub, 0, slayers.CmnHdrLen, R54)
			// @ sl.CombineAtIndex_Bytes(ub, 0, start, slayers.CmnHdrLen, R54)
			// @ ghost sl.CombineRange_Bytes(ub, start, end, writePerm)
			return errorDiscard("error", err)
		}
		// @ ghost sl.CombineRange_Bytes(ub, start, end, HalfPerm)
		// @ slayers.IsSupportedPktSubslice(ub, slayers.CmnHdrLen)
		// @ sl.Unslice_Bytes(ub, 0, slayers.CmnHdrLen, R54)
		// @ sl.CombineAtIndex_Bytes(ub, 0, start, slayers.CmnHdrLen, R54)
		// @ p.scionLayer.ValidHeaderOffsetFromSubSliceLemma(ub, start)
		// @ p.SubSliceAbsPktToAbsPkt(ub, start, end)
		// @ ghost sl.CombineRange_Bytes(ub, start, end, HalfPerm)
		// @ absPktFutureLemma(ub)
		// @ assert absPkt(ub).CurrSeg.UInfo ==
		// @ 	old(io.upd_uinfo(path.AbsUInfoFromUint16(p.infoField.SegID), p.hopField.ToIO_HF()))
		// @ assert reveal p.EqAbsInfoField(absPkt(ub))
		// @ assert reveal p.EqAbsHopField(absPkt(ub))
		// @ assert reveal p.LastHopLen(ub)
	}
	return pForward
}

// @ requires acc(p.scionLayer.Mem(ubScionL), R20)
// @ requires acc(&p.path, R50)
// @ requires p.path == p.scionLayer.GetPath(ubScionL)
// @ ensures  acc(p.scionLayer.Mem(ubScionL), R20)
// @ ensures  acc(&p.path, R50)
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
// @ requires acc(&p.path, R50)
// @ requires p.path == p.scionLayer.GetPath(ubScionL)
// @ ensures  acc(p.scionLayer.Mem(ubScionL), R20)
// @ ensures  acc(&p.path, R50)
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

// @ requires  0 <= startLL && startLL <= endLL && endLL <= len(ubScionL)
// @ requires  acc(&p.path, R20)
// @ requires  sl.Bytes(ubScionL, 0, len(ubScionL))
// @ requires  acc(p.scionLayer.Mem(ubScionL), R3)
// @ requires  p.scionLayer.ValidPathMetaData(ubScionL)
// @ requires  p.path == p.scionLayer.GetPath(ubScionL)
// @ requires  acc(&p.buffer, R50) && p.buffer != nil && p.buffer.Mem()
// @ requires   sl.Bytes(p.buffer.UBuf(), 0, len(p.buffer.UBuf()))
// @ requires  acc(&p.d, R50) && acc(p.d.Mem(), _)
// @ preserves acc(&p.ingressID, R21)
// @ requires  acc(&p.infoField, R20)
// @ requires  acc(&p.hopField, R20)
// @ preserves acc(&p.mac, R20) && p.mac != nil && p.mac.Mem()
// @ preserves acc(&p.macBuffers.scionInput, R20)
// @ preserves sl.Bytes(p.macBuffers.scionInput, 0, len(p.macBuffers.scionInput))
// @ preserves acc(&p.cachedMac)
// @ preserves ubLL == nil || ubLL === ubScionL[startLL:endLL]
// @ preserves acc(&p.lastLayer, R55) && p.lastLayer != nil
// @ preserves &p.scionLayer !== p.lastLayer ==>
// @ 	acc(p.lastLayer.Mem(ubLL), R15)
// @ preserves &p.scionLayer === p.lastLayer ==>
// @ 	ubScionL === ubLL
// @ ensures   acc(&p.path, R20)
// @ ensures   acc(&p.infoField, R20)
// @ ensures   acc(&p.hopField,  R20)
// @ ensures   acc(&p.d, R50) && acc(p.d.Mem(), _)
// @ ensures   acc(p.scionLayer.Mem(ubScionL), R3)
// @ ensures   sl.Bytes(ubScionL, 0, len(ubScionL))
// @ ensures   p.d.validResult(respr, false)
// @ ensures   acc(&p.buffer, R50) && p.buffer != nil && p.buffer.Mem()
// @ ensures   sl.Bytes(p.buffer.UBuf(), 0, len(p.buffer.UBuf()))
// @ ensures   respr !== processResult{} ==>
// @ 	respr.OutPkt === p.buffer.UBuf()
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// @ ensures   reserr == nil ==>
// @ 	respr === processResult{}
// contracts for IO-spec
// @ requires  slayers.ValidPktMetaHdr(ubScionL) && p.scionLayer.EqAbsHeader(ubScionL)
// @ requires  absPkt(ubScionL).PathNotFullyTraversed()
// @ requires  p.EqAbsHopField(absPkt(ubScionL))
// @ requires  p.EqAbsInfoField(absPkt(ubScionL))
// @ ensures   reserr == nil ==> slayers.ValidPktMetaHdr(ubScionL) && p.scionLayer.EqAbsHeader(ubScionL)
// @ ensures   reserr == nil ==> absPkt(ubScionL).PathNotFullyTraversed()
// @ ensures   reserr == nil ==> AbsVerifyCurrentMACConstraint(absPkt(ubScionL), dp)
// @ ensures   reserr == nil ==> old(slayers.IsSupportedPkt(ubScionL)) == slayers.IsSupportedPkt(ubScionL)
// @ ensures   reserr == nil ==> absPkt(ubScionL) == old(absPkt(ubScionL))
// @ ensures   reserr == nil ==> p.DstIsLocalIngressID(ubScionL) == old(p.DstIsLocalIngressID(ubScionL))
// @ ensures   reserr == nil ==> p.LastHopLen(ubScionL) == old(p.LastHopLen(ubScionL))
// @ ensures   reserr != nil && respr.OutPkt != nil ==>
// @ 	absIO_val(respr.OutPkt, respr.EgressID).isIO_val_Unsupported
// @ decreases
func (p *scionPacketProcessor) verifyCurrentMAC( /*@ ghost dp io.DataPlaneSpec, ghost ubScionL []byte, ghost ubLL []byte, ghost startLL int, ghost endLL int @*/ ) disposition {
	// @ ghost oldPkt := absPkt(ubScionL)
	fullMac := path.FullMAC(p.mac, p.infoField, p.hopField, p.macInputBuffer[:path.MACBufferSize])
	// @ fold acc(sl.Bytes(p.hopField.Mac[:path.MacLen], 0, path.MacLen), R21)
	// @ defer unfold acc(sl.Bytes(p.hopField.Mac[:path.MacLen], 0, path.MacLen), R21)
	// @ sl.SplitRange_Bytes(fullMac, 0, path.MacLen, R21)
	// @ ghost defer sl.CombineRange_Bytes(fullMac, 0, path.MacLen, R21)
	if subtle.ConstantTimeCompare(p.hopField.Mac[:path.MacLen], fullMac[:path.MacLen]) == 0 {
		// @ ghost ubPath := p.scionLayer.UBPath(ubScionL)
		// @ ghost start := p.scionLayer.PathStartIdx(ubScionL)
		// @ ghost end   := p.scionLayer.PathEndIdx(ubScionL)
		// @ assert ubScionL[start:end] === ubPath

		// @ unfold acc(p.scionLayer.Mem(ubScionL), R13)
		// @ defer fold acc(p.scionLayer.Mem(ubScionL), R13)
		// @ unfold acc(p.path.Mem(ubPath), R14)
		// @ defer fold acc(p.path.Mem(ubPath), R14)
		// @ unfold acc(p.path.Base.Mem(), R15)
		// @ defer fold acc(p.path.Base.Mem(), R15)

		log.Debug("SCMP response", "cause", macVerificationFailed,
			"expected", fullMac[:path.MacLen],
			"actual", p.hopField.Mac[:path.MacLen],
			"cons_dir", p.infoField.ConsDir,
			"if_id", p.pkt.ingress, "curr_inf", p.path.PathMeta.CurrINF,
			"curr_hf", p.path.PathMeta.CurrHF, "seg_id", p.infoField.SegID)
		p.pkt.slowPathRequest = slowPathRequest{
			scmpType: slayers.SCMPTypeParameterProblem,
			code:     slayers.SCMPCodeInvalidHopFieldMAC,
			pointer:  p.currentHopPointer(),
		}
		// @ ghost if tmpErr != nil && tmpRes.OutPkt != nil {
		// @ 	AbsUnsupportedPktIsUnsupportedVal(tmpRes.OutPkt, tmpRes.EgressID)
		// @ }
		return pSlowPath
	}
	// Add the full MAC to the SCION packet processor,
	// such that EPIC does not need to recalculate it.
	p.cachedMac = fullMac
	// @ reveal p.EqAbsInfoField(oldPkt)
	// @ reveal p.EqAbsHopField(oldPkt)
	// (VerifiedSCION) Assumptions for Cryptography:
	// @ absInf := p.infoField.ToAbsInfoField()
	// @ absHF := p.hopField.ToIO_HF()
	// @ AssumeForIO(dp.hf_valid(absInf.ConsDir, absInf.AInfo, absInf.UInfo, absHF))
	// @ reveal AbsVerifyCurrentMACConstraint(oldPkt, dp)
	// @ fold p.d.validResult(processResult{}, false)
	return pForward
}

// @ requires  0 <= startLL && startLL <= endLL && endLL <= len(ubScionL)
// @ requires  acc(&p.path, R20)
// @ requires  sl.Bytes(ubScionL, 0, len(ubScionL))
// @ requires  acc(p.scionLayer.Mem(ubScionL), R3)
// @ requires  p.scionLayer.ValidPathMetaData(ubScionL)
// @ requires  p.path == p.scionLayer.GetPath(ubScionL)
// @ requires  acc(&p.buffer, R50) && p.buffer != nil && p.buffer.Mem()
// @ requires  sl.Bytes(p.buffer.UBuf(), 0, len(p.buffer.UBuf()))
// @ requires  acc(&p.d, R15) && acc(p.d.Mem(), _)
// pres for IO:
// @ requires  slayers.ValidPktMetaHdr(ubScionL) && p.scionLayer.EqAbsHeader(ubScionL)
// @ requires  absPkt(ubScionL).PathNotFullyTraversed()
// @ preserves acc(&p.ingressID, R40)
// @ preserves ubLL == nil || ubLL === ubScionL[startLL:endLL]
// @ preserves acc(&p.lastLayer, R55) && p.lastLayer != nil
// @ preserves &p.scionLayer !== p.lastLayer ==>
// @ 	acc(p.lastLayer.Mem(ubLL), R15)
// @ preserves &p.scionLayer === p.lastLayer ==>
// @ 	ubScionL === ubLL
// @ ensures   acc(&p.d, R15) && acc(p.d.Mem(), _)
// @ requires  p.d.getValSvc() != nil
// @ ensures   p.d.validResult(respr, addrAliasesUb)
// @ ensures   !addrAliasesUb ==> acc(sl.Bytes(ubScionL, 0, len(ubScionL)), R15)
// @ ensures   !addrAliasesUb && resaddr != nil ==> acc(resaddr.Mem(), _)
// @ ensures   addrAliasesUb ==> resaddr != nil
// @ ensures   addrAliasesUb ==> acc(resaddr.Mem(), R15)
// @ ensures   addrAliasesUb ==> (acc(resaddr.Mem(), R15) --* acc(sl.Bytes(ubScionL, 0, len(ubScionL)), R15))
// @ ensures   reserr != nil ==> !addrAliasesUb
// @ ensures   acc(&p.path, R20)
// @ ensures   acc(p.scionLayer.Mem(ubScionL), R3)
// @ ensures   acc(sl.Bytes(ubScionL, 0, len(ubScionL)), 1-R15)
// @ ensures   acc(&p.buffer, R50) && p.buffer != nil && p.buffer.Mem()
// @ ensures   sl.Bytes(p.buffer.UBuf(), 0, len(p.buffer.UBuf()))
// @ ensures   respr !== processResult{} ==>
// @ 	respr.OutPkt === p.buffer.UBuf()
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// @ ensures   reserr == nil ==>
// @ 	respr === processResult{}
// posts for IO:
// @ ensures   reserr == nil ==> slayers.ValidPktMetaHdr(ubScionL) && p.scionLayer.EqAbsHeader(ubScionL)
// @ ensures   reserr == nil ==> absPkt(ubScionL).PathNotFullyTraversed()
// @ ensures   reserr == nil ==> absPkt(ubScionL) == old(absPkt(ubScionL))
// @ ensures   reserr == nil ==> old(slayers.IsSupportedPkt(ubScionL)) == slayers.IsSupportedPkt(ubScionL)
// @ ensures   reserr != nil && respr.OutPkt != nil ==>
// @ 	absIO_val(respr.OutPkt, respr.EgressID).isIO_val_Unsupported
// @ decreases 0 if sync.IgnoreBlockingForTermination()
func (p *scionPacketProcessor) resolveInbound( /*@ ghost ubScionL []byte, ghost ubLL []byte, ghost startLL int, ghost endLL int @*/ ) (dsp disposition /*@ , ghost addrAliasesUb bool @*/) {
	// (VerifiedSCION) the parameter used to be p.scionLayer,
	// instead of &p.scionLayer. Process was lost when merging (abojarski).

	err := p.d.resolveLocalDst(p.pkt.dstAddr, p.scionLayer, p.lastLayer)
	// @ establishNoSVCBackend()
	switch err {
	case nil:
		return pForward
	case noSVCBackend:
		log.Debug("SCMP response", "cause", err)
		p.pkt.slowPathRequest = slowPathRequest{
			scmpType: slayers.SCMPTypeDestinationUnreachable,
			code:     slayers.SCMPCodeNoRoute,
		}
		return pSlowPath
	case invalidDstAddr, unsupportedV4MappedV6Address, unsupportedUnspecifiedAddress:
		log.Debug("SCMP response", "cause", err)
		p.pkt.slowPathRequest = slowPathRequest{
			scmpType: slayers.SCMPTypeParameterProblem,
			code:     slayers.SCMPCodeInvalidDestinationAddress,
		}
		return pSlowPath
	default:
		return errorDiscard("error", err)
	}
}

// @ requires acc(&p.path, R20)
// @ requires p.scionLayer.Mem(ub)
// @ requires p.path === p.scionLayer.GetPath(ub)
// @ requires sl.Bytes(ub, 0, len(ub))
// @ requires acc(&p.infoField)
// @ requires acc(&p.hopField, R20)
// @ requires !p.GetIsXoverSpec(ub)
// Preconditions for IO:
// @ requires slayers.ValidPktMetaHdr(ub) && p.scionLayer.EqAbsHeader(ub)
// @ requires absPkt(ub).PathNotFullyTraversed()
// @ requires p.EqAbsHopField(absPkt(ub))
// @ requires p.EqAbsInfoField(absPkt(ub))
// @ ensures  acc(&p.infoField)
// @ ensures  acc(&p.hopField, R20)
// @ ensures  sl.Bytes(ub, 0, len(ub))
// @ ensures  acc(&p.path, R20)
// @ ensures  reserr == nil ==> p.scionLayer.Mem(ub)
// @ ensures  reserr != nil ==> p.scionLayer.NonInitMem()
// @ ensures  reserr != nil ==> reserr.ErrorMem()
// Postconditions for IO:
// @ ensures  reserr == nil ==> slayers.ValidPktMetaHdr(ub) && p.scionLayer.EqAbsHeader(ub)
// @ ensures  reserr == nil ==> len(absPkt(ub).CurrSeg.Future) >= 0
// @ ensures  reserr == nil ==> absPkt(ub) == AbsProcessEgress(old(absPkt(ub)))
// @ ensures  reserr == nil ==> old(slayers.IsSupportedPkt(ub)) == slayers.IsSupportedPkt(ub)
// @ decreases
func (p *scionPacketProcessor) processEgress( /*@ ghost ub []byte @*/ ) disposition {
	// We are the egress router and if we go in construction direction we
	// need to update the SegID (unless we are effecting a peering hop).
	// When we're at a peering hop, the SegID for this hop and for the next
	// are one and the same, both hops chain to the same parent. So do not
	// update SegID.
	// @ ghost ubPath := p.scionLayer.UBPath(ub)
	// @ ghost startP := p.scionLayer.PathStartIdx(ub)
	// @ ghost endP   := p.scionLayer.PathEndIdx(ub)
	// @ assert ub[startP:endP] === ubPath

	// @ unfold acc(p.scionLayer.Mem(ub), 1-R55)
	// @ sl.SplitRange_Bytes(ub, startP, endP, HalfPerm)
	// @ sl.SplitByIndex_Bytes(ub, 0, startP, slayers.CmnHdrLen, R54)
	// @ sl.Reslice_Bytes(ub, 0, slayers.CmnHdrLen, R54)
	// @ slayers.IsSupportedPktSubslice(ub, slayers.CmnHdrLen)
	// @ p.AbsPktToSubSliceAbsPkt(ub, startP, endP)
	// @ p.scionLayer.ValidHeaderOffsetToSubSliceLemma(ub, startP)
	// @ reveal p.EqAbsInfoField(absPkt(ub))
	// @ reveal p.EqAbsHopField(absPkt(ub))
	// @ sl.SplitRange_Bytes(ub, startP, endP, HalfPerm)
	// @ reveal p.scionLayer.ValidHeaderOffset(ub, startP)
	// @ unfold acc(p.scionLayer.Mem(ub), R55)
	if p.infoField.ConsDir && !p.peering {
		p.infoField.UpdateSegID(p.hopField.Mac /*@, p.hopField.ToIO_HF() @*/)
		// @ assert path.AbsUInfoFromUint16(p.infoField.SegID) ==
		// @ 	old(io.upd_uinfo(path.AbsUInfoFromUint16(p.infoField.SegID), p.hopField.ToIO_HF()))
		// @ assume 0 <= p.path.GetCurrINF(ubPath)

		if err := p.path.SetInfoField(p.infoField, int( /*@ unfolding acc(p.path.Mem(ubPath), R45) in (unfolding acc(p.path.Base.Mem(), R50) in @*/ p.path.PathMeta.CurrINF /*@ ) @*/) /*@ , ubPath @*/); err != nil {
			// TODO parameter problem invalid path
			// @ sl.Unslice_Bytes(ub, 0, slayers.CmnHdrLen, R54)
			// @ sl.CombineAtIndex_Bytes(ub, 0, startP, slayers.CmnHdrLen, R54)
			// @ ghost sl.CombineRange_Bytes(ub, startP, endP, writePerm)
			// @ p.path.DowngradePerm(ubPath)
			// @ p.scionLayer.PathPoolMemExchange(p.scionLayer.PathType, p.scionLayer.Path)
			// @ unfold p.scionLayer.HeaderMem(ub[slayers.CmnHdrLen:])
			// @ fold p.scionLayer.NonInitMem()
			return errorDiscard("error", err)
		}
	}
	if err := p.path.IncPath( /*@ ubPath @*/ ); err != nil {
		// @ sl.Unslice_Bytes(ub, 0, slayers.CmnHdrLen, R54)
		// @ sl.CombineAtIndex_Bytes(ub, 0, startP, slayers.CmnHdrLen, R54)
		// @ ghost sl.CombineRange_Bytes(ub, startP, endP, writePerm)
		// @ p.scionLayer.PathPoolMemExchange(p.scionLayer.PathType, p.scionLayer.Path)
		// @ unfold p.scionLayer.HeaderMem(ub[slayers.CmnHdrLen:])
		// @ fold p.scionLayer.NonInitMem()
		// TODO parameter problem invalid path
		return errorDiscard("error", err)
	}
	// @ fold acc(p.scionLayer.Mem(ub), R55)
	// @ assert reveal p.scionLayer.ValidHeaderOffset(ub, startP)
	// @ ghost sl.CombineRange_Bytes(ub, startP, endP, HalfPerm)
	// @ slayers.IsSupportedPktSubslice(ub, slayers.CmnHdrLen)
	// @ sl.Unslice_Bytes(ub, 0, slayers.CmnHdrLen, R54)
	// @ sl.CombineAtIndex_Bytes(ub, 0, startP, slayers.CmnHdrLen, R54)
	// @ p.scionLayer.ValidHeaderOffsetFromSubSliceLemma(ub, startP)
	// @ p.SubSliceAbsPktToAbsPkt(ub, startP, endP)
	// @ ghost sl.CombineRange_Bytes(ub, startP, endP, HalfPerm)
	// @ absPktFutureLemma(ub)
	// @ assert absPkt(ub) == reveal AbsProcessEgress(old(absPkt(ub)))
	// @ fold acc(p.scionLayer.Mem(ub), 1-R55)
	return pForward
}

// @ requires acc(&p.path, R20)
// @ requires p.scionLayer.Mem(ub)
// @ requires p.path == p.scionLayer.GetPath(ub)
// @ requires sl.Bytes(ub, 0, len(ub))
// @ requires acc(&p.segmentChange)
// @ requires acc(&p.hopField)
// @ requires acc(&p.infoField)
// Preconditions for IO:
// @ requires slayers.ValidPktMetaHdr(ub) && p.scionLayer.EqAbsHeader(ub)
// @ requires p.GetIsXoverSpec(ub)
// @ requires let ubPath := p.scionLayer.UBPath(ub) in
// @ 	(unfolding acc(p.scionLayer.Mem(ub), _) in p.path.GetBase(ubPath)) == currBase
// @ requires currBase.Valid()
// @ ensures  acc(&p.segmentChange)
// @ ensures  acc(&p.hopField)
// @ ensures  acc(&p.infoField)
// @ ensures  sl.Bytes(ub, 0, len(ub))
// @ ensures  acc(&p.path, R20)
// @ ensures  reserr == nil ==> p.scionLayer.Mem(ub)
// @ ensures  reserr == nil ==> p.scionLayer.UBPath(ub) === old(p.scionLayer.UBPath(ub))
// @ ensures  reserr == nil ==> p.scionLayer.GetPath(ub) == old(p.scionLayer.GetPath(ub))
// @ ensures  reserr != nil ==> p.scionLayer.NonInitMem()
// @ ensures  p.segmentChange
// @ ensures  respr === processResult{}
// @ ensures  reserr != nil ==> reserr.ErrorMem()
// Postconditions for IO:
// @ ensures  reserr == nil ==> len(old(absPkt(ub)).CurrSeg.Future) == 1
// @ ensures  reserr == nil ==> old(absPkt(ub)).LeftSeg != none[io.IO_seg2]
// @ ensures  reserr == nil ==> len(get(old(absPkt(ub)).LeftSeg).Future) > 0
// @ ensures  reserr == nil ==> len(get(old(absPkt(ub)).LeftSeg).History) == 0
// @ ensures  reserr == nil ==> slayers.ValidPktMetaHdr(ub) && p.scionLayer.EqAbsHeader(ub)
// @ ensures  reserr == nil ==> absPkt(ub).PathNotFullyTraversed()
// @ ensures  reserr == nil ==> p.EqAbsHopField(absPkt(ub))
// @ ensures  reserr == nil ==> p.EqAbsInfoField(absPkt(ub))
// @ ensures  reserr == nil ==> absPkt(ub) == AbsDoXover(old(absPkt(ub)))
// @ ensures  reserr == nil ==>
// @ 	old(slayers.IsSupportedPkt(ub)) == slayers.IsSupportedPkt(ub)
// @ ensures  reserr == nil ==>
// @ 	let ubPath := p.scionLayer.UBPath(ub)   in
// @ 	(unfolding acc(p.scionLayer.Mem(ub), _) in
// @ 	p.path === p.scionLayer.GetPath(ub) &&
// @ 	p.path.GetBase(ubPath) == currBase.IncPathSpec() &&
// @ 	currBase.IncPathSpec().Valid())
// @ ensures   reserr == nil ==>
// @ 	p.scionLayer.ValidPathMetaData(ub) == old(p.scionLayer.ValidPathMetaData(ub))
// @ decreases
func (p *scionPacketProcessor) doXover( /*@ ghost ub []byte, ghost currBase scion.Base @*/ ) disposition {
	p.effectiveXover = true
	// @ ghost  startP := p.scionLayer.PathStartIdx(ub)
	// @ ghost  endP   := p.scionLayer.PathEndIdx(ub)
	// @ ghost  ubPath := ub[startP:endP]

	// @ unfold acc(p.scionLayer.Mem(ub), 1-R55)
	// @ sl.SplitRange_Bytes(ub, startP, endP, HalfPerm)
	// @ sl.SplitByIndex_Bytes(ub, 0, startP, slayers.CmnHdrLen, R54)
	// @ sl.Reslice_Bytes(ub, 0, slayers.CmnHdrLen, R54)
	// @ slayers.IsSupportedPktSubslice(ub, slayers.CmnHdrLen)
	// @ p.AbsPktToSubSliceAbsPkt(ub, startP, endP)
	// @ p.scionLayer.ValidHeaderOffsetToSubSliceLemma(ub, startP)
	// @ p.path.XoverLemma(ubPath)
	// @ reveal p.EqAbsInfoField(absPkt(ub))
	// @ reveal p.EqAbsHopField(absPkt(ub))
	// @ sl.SplitRange_Bytes(ub, startP, endP, HalfPerm)
	// @ reveal p.scionLayer.ValidHeaderOffset(ub, startP)
	// @ unfold acc(p.scionLayer.Mem(ub), R55)
	if err := p.path.IncPath( /*@ ubPath @*/ ); err != nil {
		// TODO parameter problem invalid path
		// (VerifiedSCION) we currently expose a lot of internal information from slayers here. Can we avoid it?
		// @ sl.Unslice_Bytes(ub, 0, slayers.CmnHdrLen, R54)
		// @ sl.CombineAtIndex_Bytes(ub, 0, startP, slayers.CmnHdrLen, R54)
		// @ ghost sl.CombineRange_Bytes(ub, startP, endP, writePerm)
		// @ unfold p.scionLayer.HeaderMem(ub[slayers.CmnHdrLen:])
		// @ p.scionLayer.PathPoolMemExchange(p.scionLayer.PathType, p.scionLayer.Path)
		// @ fold p.scionLayer.NonInitMem()
		return errorDiscard("error", err)
	}
	// @ fold acc(p.scionLayer.Mem(ub), R55)
	// @ assert reveal p.scionLayer.ValidHeaderOffset(ub, startP)
	// @ ghost sl.CombineRange_Bytes(ub, startP, endP, HalfPerm)
	// @ slayers.IsSupportedPktSubslice(ub, slayers.CmnHdrLen)
	// @ sl.Unslice_Bytes(ub, 0, slayers.CmnHdrLen, R54)
	// @ sl.CombineAtIndex_Bytes(ub, 0, startP, slayers.CmnHdrLen, R54)
	// @ p.scionLayer.ValidHeaderOffsetFromSubSliceLemma(ub, startP)
	// @ p.SubSliceAbsPktToAbsPkt(ub, startP, endP)
	// @ assert len(get(old(absPkt(ub)).LeftSeg).Future) > 0
	// @ assert len(get(old(absPkt(ub)).LeftSeg).History) == 0
	// @ assert slayers.ValidPktMetaHdr(ub) && p.scionLayer.EqAbsHeader(ub)
	// @ assert absPkt(ub) == reveal AbsDoXover(old(absPkt(ub)))
	var err error
	// (VerifiedSCION) Due to an incompleteness (https://github.com/viperproject/gobra/issues/770),
	// we introduce a temporary variable to be able to call `path.AbsMacArrayCongruence()`.
	var tmpHopField path.HopField
	if tmpHopField, err = p.path.GetCurrentHopField( /*@ ubPath @*/ ); err != nil {
		// @ ghost sl.CombineRange_Bytes(ub, startP, endP, writePerm)
		// @ fold acc(p.scionLayer.Mem(ub), 1-R55)
		// @ p.scionLayer.DowngradePerm(ub)
		// TODO parameter problem invalid path
		return errorDiscard("error", err)
	}
	p.hopField = tmpHopField
	// @ path.AbsMacArrayCongruence(p.hopField.Mac, tmpHopField.Mac)
	// @ assert p.hopField.ToIO_HF() == tmpHopField.ToIO_HF()
	// @ assert reveal p.path.CorrectlyDecodedHf(ubPath, tmpHopField)
	// @ assert reveal p.path.CorrectlyDecodedHf(ubPath, p.hopField)
	if p.infoField, err = p.path.GetCurrentInfoField( /*@ ubPath @*/ ); err != nil {
		// @ ghost sl.CombineRange_Bytes(ub, startP, endP, writePerm)
		// @ fold acc(p.scionLayer.Mem(ub), 1-R55)
		// @ p.scionLayer.DowngradePerm(ub)
		// TODO parameter problem invalid path
		return errorDiscard("error", err)
	}
	// @ ghost sl.CombineRange_Bytes(ub, startP, endP, HalfPerm)
	// @ p.SubSliceAbsPktToAbsPkt(ub, startP, endP)
	// @ absPktFutureLemma(ub)
	// @ p.path.DecodingLemma(ubPath, p.infoField, p.hopField)
	// @ assert reveal p.path.EqAbsInfoField(p.path.absPkt(ubPath), p.infoField.ToAbsInfoField())
	// @ assert reveal p.path.EqAbsHopField(p.path.absPkt(ubPath), p.hopField.ToIO_HF())
	// @ assert reveal p.EqAbsHopField(absPkt(ub))
	// @ assert reveal p.EqAbsInfoField(absPkt(ub))
	// @ fold acc(p.scionLayer.Mem(ub), 1-R55)
	return pForward
}

// @ requires  acc(&p.path, R20)
// @ requires  acc(p.path.Mem(ubPath), R5)
// @ requires  acc(&p.infoField, R5) && acc(&p.hopField, R5)
// @ requires  p.path.GetCurrINF(ubPath) <= p.path.GetNumINF(ubPath)
// @ requires  p.path.GetCurrHF(ubPath) <= p.path.GetNumHops(ubPath)
// @ preserves acc(sl.Bytes(ubPath, 0, len(ubPath)), R5)
// @ ensures   acc(&p.path, R20)
// @ ensures   acc(p.path.Mem(ubPath), R5)
// @ ensures   acc(&p.infoField, R5) && acc(&p.hopField, R5)
// @ decreases
func (p *scionPacketProcessor) ingressInterface( /*@ ghost ubPath []byte @*/ ) uint16 {
	info := p.infoField
	hop := p.hopField
	if !p.peering && p.path.IsFirstHopAfterXover( /*@ ubPath @*/ ) {
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

// @ requires acc(&p.infoField, R21)
// @ requires acc(&p.hopField, R21)
// pres for IO:
// @ requires oldPkt.PathNotFullyTraversed()
// @ requires p.EqAbsInfoField(oldPkt)
// @ requires p.EqAbsHopField(oldPkt)
// @ ensures  acc(&p.infoField, R21)
// @ ensures  acc(&p.hopField, R21)
// posts for IO:
// @ ensures  p.EqAbsInfoField(oldPkt)
// @ ensures  p.EqAbsHopField(oldPkt)
// @ ensures  AbsEgressInterfaceConstraint(oldPkt, path.ifsToIO_ifs(egress))
// @ decreases
func (p *scionPacketProcessor) egressInterface( /*@ ghost oldPkt io.IO_pkt2 @*/ ) (egress uint16) {
	// @ reveal p.EqAbsInfoField(oldPkt)
	// @ reveal p.EqAbsHopField(oldPkt)
	if p.infoField.ConsDir {
		// @ assert reveal AbsEgressInterfaceConstraint(oldPkt, path.ifsToIO_ifs(p.hopField.ConsEgress))
		return p.hopField.ConsEgress
	}
	// @ assert reveal AbsEgressInterfaceConstraint(oldPkt, path.ifsToIO_ifs(p.hopField.ConsIngress))
	return p.hopField.ConsIngress
}

// @ requires  0 <= startLL && startLL <= endLL && endLL <= len(ub)
// @ requires  acc(&p.path, R20)
// @ requires  sl.Bytes(ub, 0, len(ub))
// @ requires  acc(p.scionLayer.Mem(ub), R2)
// @ requires  p.scionLayer.ValidPathMetaData(ub)
// @ requires  p.path == p.scionLayer.GetPath(ub)
// @ requires  acc(&p.buffer, R50) && p.buffer != nil && p.buffer.Mem()
// @ requires   sl.Bytes(p.buffer.UBuf(), 0, len(p.buffer.UBuf()))
// @ requires  acc(&p.d, R50) && acc(p.d.Mem(), _)
// @ requires  acc(&p.infoField, R20)
// @ requires  acc(&p.hopField, R20)
// @ requires  acc(&p.ingressID, R21)
// pres for IO:
// @ requires  slayers.ValidPktMetaHdr(ub) && p.scionLayer.EqAbsHeader(ub)
// @ requires  absPkt(ub).PathNotFullyTraversed()
// @ requires  p.EqAbsInfoField(absPkt(ub))
// @ requires  p.EqAbsHopField(absPkt(ub))
// @ preserves ubLL == nil || ubLL === ub[startLL:endLL]
// @ preserves acc(&p.lastLayer, R55) && p.lastLayer != nil
// @ preserves &p.scionLayer !== p.lastLayer ==>
// @ 	acc(p.lastLayer.Mem(ubLL), R15)
// @ preserves &p.scionLayer === p.lastLayer ==>
// @ 	ub === ubLL
// @ ensures   acc(&p.infoField, R20)
// @ ensures   acc(&p.hopField, R20)
// @ ensures   acc(&p.ingressID, R21)
// @ ensures   acc(&p.path, R20)
// @ ensures   acc(&p.d, R50) && acc(p.d.Mem(), _)
// @ ensures   acc(p.scionLayer.Mem(ub), R2)
// @ ensures   sl.Bytes(ub, 0, len(ub))
// @ ensures   p.d.validResult(respr, false)
// @ ensures   acc(&p.buffer, R50) && p.buffer != nil && p.buffer.Mem()
// @ ensures   sl.Bytes(p.buffer.UBuf(), 0, len(p.buffer.UBuf()))
// @ ensures   respr !== processResult{} ==>
// @ 	respr.OutPkt === p.buffer.UBuf()
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// @ ensures   reserr == nil ==>
// @ 	respr === processResult{}
// posts for IO:
// @ ensures reserr == nil ==> slayers.ValidPktMetaHdr(ub) && p.scionLayer.EqAbsHeader(ub)
// @ ensures reserr == nil ==> old(slayers.IsSupportedPkt(ub)) == slayers.IsSupportedPkt(ub)
// @ ensures reserr == nil ==> absPkt(ub) == old(absPkt(ub))
// @ ensures   reserr != nil && respr.OutPkt != nil ==>
// @ 	absIO_val(respr.OutPkt, respr.EgressID).isIO_val_Unsupported
// @ decreases 0 if sync.IgnoreBlockingForTermination()
func (p *scionPacketProcessor) validateEgressUp(
// @ 	ghost ub []byte,
// @ 	ghost ubLL []byte,
// @ 	ghost startLL int,
// @ 	ghost endLL int,
) disposition {
	// @ ghost oldPkt := absPkt(ub)
	egressID := p.pkt.egress
	// @ p.d.getBfdSessionsMem()
	// @ ghost if p.d.bfdSessions != nil { unfold acc(accBfdSession(p.d.bfdSessions), _) }
	if v, ok := p.d.bfdSessions[egressID]; ok {
		if !v.IsUp() {
			// @ p.d.getLocalIA()
			log.Debug("SCMP response", "cause", errBFDSessionDown)
			// @ p.d.getExternalMem()
			// @ if p.d.external != nil { unfold acc(accBatchConn(p.d.external), _) }
			if _, external := p.d.external[p.pkt.egress]; !external {
				p.pkt.slowPathRequest = slowPathRequest{
					scmpType: slayers.SCMPTypeInternalConnectivityDown,
					code:     0,
				}
			} else {
				p.pkt.slowPathRequest = slowPathRequest{
					scmpType: slayers.SCMPTypeExternalInterfaceDown,
					code:     0,
				}
			}
			return pSlowPath
		}
	}
	return pForward
}

// @ requires  0 <= startLL && startLL <= endLL && endLL <= len(ub)
// @ requires  acc(&p.path, R20)
// @ requires  sl.Bytes(ub, 0, len(ub))
// @ requires  acc(p.scionLayer.Mem(ub), R3)
// @ requires  p.scionLayer.ValidPathMetaData(ub)
// @ requires  p.path == p.scionLayer.GetPath(ub)
// @ requires  acc(&p.buffer, R50) && p.buffer != nil && p.buffer.Mem()
// @ requires  sl.Bytes(p.buffer.UBuf(), 0, len(p.buffer.UBuf()))
// @ requires  acc(&p.d, R50) && acc(p.d.Mem(), _)
// @ requires  acc(&p.ingressID, R21)
// @ requires  acc(&p.infoField, R20)
// @ requires  acc(&p.hopField)
// @ preserves acc(&p.mac, R20) && p.mac != nil && p.mac.Mem()
// @ preserves acc(&p.macBuffers.scionInput, R20)
// @ preserves sl.Bytes(p.macBuffers.scionInput, 0, len(p.macBuffers.scionInput))
// @ preserves acc(&p.cachedMac)
// @ preserves ubLL == nil || ubLL === ub[startLL:endLL]
// @ preserves acc(&p.lastLayer, R55) && p.lastLayer != nil
// @ preserves &p.scionLayer !== p.lastLayer ==>
// @ 	acc(p.lastLayer.Mem(ubLL), R15)
// @ preserves &p.scionLayer === p.lastLayer ==>
// @ 	ub === ubLL
// @ ensures   acc(&p.ingressID, R21)
// @ ensures   acc(&p.path, R20)
// @ ensures   acc(&p.infoField, R20)
// @ ensures   acc(&p.hopField)
// @ ensures   acc(&p.d, R50) && acc(p.d.Mem(), _)
// @ ensures   acc(p.scionLayer.Mem(ub), R3)
// @ ensures   sl.Bytes(ub, 0, len(ub))
// @ ensures   p.d.validResult(respr, false)
// @ ensures   acc(&p.buffer, R50) && p.buffer != nil && p.buffer.Mem()
// @ ensures   sl.Bytes(p.buffer.UBuf(), 0, len(p.buffer.UBuf()))
// @ ensures   respr !== processResult{} ==>
// @ 	respr.OutPkt === p.buffer.UBuf()
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// @ ensures   reserr == nil ==>
// @ 	respr === processResult{}
// constracts for IO-spec
// @ requires  slayers.ValidPktMetaHdr(ub) && p.scionLayer.EqAbsHeader(ub)
// @ requires  p.DstIsLocalIngressID(ub)
// @ requires  p.LastHopLen(ub)
// @ requires  absPkt(ub).PathNotFullyTraversed()
// @ requires  p.EqAbsHopField(absPkt(ub))
// @ ensures   reserr == nil ==> slayers.ValidPktMetaHdr(ub) && p.scionLayer.EqAbsHeader(ub)
// @ ensures   reserr == nil ==> p.DstIsLocalIngressID(ub)
// @ ensures   reserr == nil ==> p.LastHopLen(ub)
// @ ensures   reserr == nil ==> absPkt(ub).PathNotFullyTraversed()
// @ ensures   reserr == nil ==> p.EqAbsHopField(absPkt(ub))
// @ ensures   reserr == nil ==> absPkt(ub) == old(absPkt(ub))
// @ ensures   reserr == nil ==> old(slayers.IsSupportedPkt(ub)) == slayers.IsSupportedPkt(ub)
// @ ensures   reserr != nil && respr.OutPkt != nil ==>
// @ 	absIO_val(respr.OutPkt, respr.EgressID).isIO_val_Unsupported
// @ decreases
func (p *scionPacketProcessor) handleIngressRouterAlert(/*@ ghost ub []byte, ghost ubLL []byte, ghost startLL int, ghost endLL int @*/ ) disposition {
	// @ reveal p.EqAbsHopField(absPkt(ub))
	// @ assert let fut := absPkt(ub).CurrSeg.Future in
	// @ 	fut == seq[io.IO_HF]{p.hopField.ToIO_HF()} ++ fut[1:]
	// @ ghost ubPath := p.scionLayer.UBPath(ub)
	// @ ghost startP := p.scionLayer.PathStartIdx(ub)
	// @ ghost endP   := p.scionLayer.PathEndIdx(ub)
	// @ assert ub[startP:endP] === ubPath
	if p.pkt.ingress == 0 {
		return pForward
	}
	alert := p.ingressRouterAlertFlag()
	if !*alert {
		return pForward
	}
	*alert = false
	// @ unfold acc(p.scionLayer.Mem(ub), R20)
	// (VerifiedSCION) the following is guaranteed by the type system, but Gobra cannot prove it yet
	// @ assume 0 <= p.path.GetCurrHF(ubPath)
	// @ reveal p.LastHopLen(ub)
	// @ sl.SplitRange_Bytes(ub, startP, endP, HalfPerm)
	// @ sl.SplitByIndex_Bytes(ub, 0, startP, slayers.CmnHdrLen, R54)
	// @ sl.Reslice_Bytes(ub, 0, slayers.CmnHdrLen, R54)
	// @ slayers.IsSupportedPktSubslice(ub, slayers.CmnHdrLen)
	// @ p.AbsPktToSubSliceAbsPkt(ub, startP, endP)
	// @ p.scionLayer.ValidHeaderOffsetToSubSliceLemma(ub, startP)
	// @ sl.SplitRange_Bytes(ub, startP, endP, HalfPerm)
	if err := p.path.SetHopField(p.hopField, int(p.path.PathMeta.CurrHF)); err != nil {
		// @ sl.Unslice_Bytes(ub, 0, slayers.CmnHdrLen, R54)
		// @ sl.CombineAtIndex_Bytes(ub, 0, startP, slayers.CmnHdrLen, R54)
		// @ sl.CombineRange_Bytes(ub, startP, endP, writePerm)
		// @ fold acc(p.scionLayer.Mem(ub), R20)
		// @ fold p.d.validResult(processResult{}, false)
		return errorDiscard("error", err)
	}
	p.pkt.slowPathRequest = slowPathRequest{
		typ: slowPathRouterAlertIngress,
	}
	// @ sl.CombineRange_Bytes(ub, startP, endP, HalfPerm)
	// @ slayers.IsSupportedPktSubslice(ub, slayers.CmnHdrLen)
	// @ sl.Unslice_Bytes(ub, 0, slayers.CmnHdrLen, R54)
	// @ sl.CombineAtIndex_Bytes(ub, 0, startP, slayers.CmnHdrLen, R54)
	// @ p.scionLayer.ValidHeaderOffsetFromSubSliceLemma(ub, startP)
	// @ p.SubSliceAbsPktToAbsPkt(ub, startP, endP)
	// @ absPktFutureLemma(ub)
	// @ assert reveal p.EqAbsHopField(absPkt(ub))
	// @ assert reveal p.LastHopLen(ub)
	// @ assert p.scionLayer.EqAbsHeader(ub)
	// @ sl.CombineRange_Bytes(ub, startP, endP, HalfPerm)
	// @ fold acc(p.scionLayer.Mem(ub), R20)
	return pSlowPath
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
// @ requires  sl.Bytes(ub, 0, len(ub))
// @ requires  acc(p.scionLayer.Mem(ub), R3)
// @ requires  p.scionLayer.ValidPathMetaData(ub)
// @ requires  p.path == p.scionLayer.GetPath(ub)
// @ requires  acc(&p.buffer, R50) && p.buffer != nil && p.buffer.Mem()
// @ requires  sl.Bytes(p.buffer.UBuf(), 0, len(p.buffer.UBuf()))
// @ requires  acc(&p.d, R50) && acc(p.d.Mem(), _)
// @ requires  acc(&p.ingressID, R21)
// @ requires  acc(&p.infoField, R20)
// @ requires  acc(&p.hopField)
// @ preserves acc(&p.mac, R20) && p.mac != nil && p.mac.Mem()
// @ preserves acc(&p.macBuffers.scionInput, R20)
// @ preserves sl.Bytes(p.macBuffers.scionInput, 0, len(p.macBuffers.scionInput))
// @ preserves acc(&p.cachedMac)
// @ preserves ubLL == nil || ubLL === ub[startLL:endLL]
// @ preserves acc(&p.lastLayer, R55) && p.lastLayer != nil
// @ preserves &p.scionLayer !== p.lastLayer ==>
// @ 	acc(p.lastLayer.Mem(ubLL), R15)
// @ preserves &p.scionLayer === p.lastLayer ==>
// @ 	ub === ubLL
// @ ensures   acc(&p.ingressID, R21)
// @ ensures   acc(&p.path, R20)
// @ ensures   acc(&p.infoField, R20)
// @ ensures   acc(&p.hopField)
// @ ensures   acc(&p.d, R50) && acc(p.d.Mem(), _)
// @ ensures   acc(p.scionLayer.Mem(ub), R3)
// @ ensures   sl.Bytes(ub, 0, len(ub))
// @ ensures   p.d.validResult(respr, false)
// @ ensures   acc(&p.buffer, R50) && p.buffer != nil && p.buffer.Mem()
// @ ensures   sl.Bytes(p.buffer.UBuf(), 0, len(p.buffer.UBuf()))
// @ ensures   respr !== processResult{} ==>
// @ 	respr.OutPkt === p.buffer.UBuf()
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// @ ensures   reserr == nil ==>
// @ 	respr === processResult{}
// constracts for IO-spec
// @ requires slayers.ValidPktMetaHdr(ub) && p.scionLayer.EqAbsHeader(ub)
// @ requires absPkt(ub).PathNotFullyTraversed()
// @ requires p.EqAbsHopField(absPkt(ub))
// @ requires p.EqAbsInfoField(absPkt(ub))
// @ ensures reserr == nil ==> slayers.ValidPktMetaHdr(ub) && p.scionLayer.EqAbsHeader(ub)
// @ ensures reserr == nil ==> absPkt(ub).PathNotFullyTraversed()
// @ ensures reserr == nil ==> p.EqAbsHopField(absPkt(ub))
// @ ensures reserr == nil ==> p.EqAbsInfoField(absPkt(ub))
// @ ensures reserr == nil ==> absPkt(ub) == old(absPkt(ub))
// @ ensures reserr == nil ==> old(slayers.IsSupportedPkt(ub)) == slayers.IsSupportedPkt(ub)
// @ ensures   reserr != nil && respr.OutPkt != nil ==>
// @ 	absIO_val(respr.OutPkt, respr.EgressID).isIO_val_Unsupported
// @ decreases
func (p *scionPacketProcessor) handleEgressRouterAlert( /*@ ghost ub []byte, ghost ubLL []byte, ghost startLL int, ghost endLL int @*/ ) disposition {
	// @ reveal p.EqAbsHopField(absPkt(ub))
	// @ assert let fut := absPkt(ub).CurrSeg.Future in
	// @ 	fut == seq[io.IO_HF]{p.hopField.ToIO_HF()} ++ fut[1:]
	// @ ghost ubPath := p.scionLayer.UBPath(ub)
	// @ ghost startP := p.scionLayer.PathStartIdx(ub)
	// @ ghost endP   := p.scionLayer.PathEndIdx(ub)
	// @ assert ub[startP:endP] === ubPath
	alert := p.egressRouterAlertFlag()
	if !*alert {
		// @ fold p.d.validResult(processResult{}, false)
		return pForward
	}
	// @ p.d.getExternalMem()
	// @ if p.d.external != nil { unfold acc(accBatchConn(p.d.external), _) }
	if _, ok := p.d.external[p.pkt.egress]; !ok {
		return pForward
	}
	*alert = false
	// @ unfold acc(p.scionLayer.Mem(ub), R20)
	// (VerifiedSCION) the following is guaranteed by the type system,
	// but Gobra cannot prove it yet
	// @ assume 0 <= p.path.GetCurrHF(ubPath)
	// @ sl.SplitRange_Bytes(ub, startP, endP, HalfPerm)
	// @ sl.SplitByIndex_Bytes(ub, 0, startP, slayers.CmnHdrLen, R54)
	// @ sl.Reslice_Bytes(ub, 0, slayers.CmnHdrLen, R54)
	// @ slayers.IsSupportedPktSubslice(ub, slayers.CmnHdrLen)
	// @ p.AbsPktToSubSliceAbsPkt(ub, startP, endP)
	// @ p.scionLayer.ValidHeaderOffsetToSubSliceLemma(ub, startP)
	// @ sl.SplitRange_Bytes(ub, startP, endP, HalfPerm)
	if err := p.path.SetHopField(p.hopField, int(p.path.PathMeta.CurrHF)); err != nil {
		// @ sl.Unslice_Bytes(ub, 0, slayers.CmnHdrLen, R54)
		// @ sl.CombineAtIndex_Bytes(ub, 0, startP, slayers.CmnHdrLen, R54)
		// @ sl.CombineRange_Bytes(ub, startP, endP, writePerm)
		// @ fold acc(p.scionLayer.Mem(ub), R20)
		// @ fold p.d.validResult(processResult{}, false)
		return errorDiscard("error", err)
	}
	p.pkt.slowPathRequest = slowPathRequest{
		typ: slowPathRouterAlertEgress,
	}
	// @ sl.CombineRange_Bytes(ub, startP, endP, HalfPerm)
	// @ slayers.IsSupportedPktSubslice(ub, slayers.CmnHdrLen)
	// @ sl.Unslice_Bytes(ub, 0, slayers.CmnHdrLen, R54)
	// @ sl.CombineAtIndex_Bytes(ub, 0, startP, slayers.CmnHdrLen, R54)
	// @ p.scionLayer.ValidHeaderOffsetFromSubSliceLemma(ub, startP)
	// @ p.SubSliceAbsPktToAbsPkt(ub, startP, endP)
	// @ absPktFutureLemma(ub)
	// @ assert reveal p.EqAbsHopField(absPkt(ub))
	// @ assert reveal p.EqAbsInfoField(absPkt(ub))
	// @ sl.CombineRange_Bytes(ub, startP, endP, HalfPerm)
	// @ fold acc(p.scionLayer.Mem(ub), R20)
	return pSlowPath
}

// @ preserves acc(&p.infoField, R21)
// @ ensures   res == &p.hopField.IngressRouterAlert || res == &p.hopField.EgressRouterAlert
// @ decreases
func (p *scionPacketProcessor) egressRouterAlertFlag() (res *bool) {
	if !p.infoField.ConsDir {
		return &p.hopField.IngressRouterAlert
	}
	return &p.hopField.EgressRouterAlert
}

// @ requires  0 <= startLL && startLL <= endLL && endLL <= len(ubScionL)
// @ requires  acc(&p.path, R20)
// @ requires  sl.Bytes(ubScionL, 0, len(ubScionL))
// @ requires  acc(p.scionLayer.Mem(ubScionL), R3)
// @ requires  p.scionLayer.ValidPathMetaData(ubScionL)
// @ requires  p.path == p.scionLayer.GetPath(ubScionL)
// @ requires  acc(&p.buffer, R50) && p.buffer != nil && p.buffer.Mem()
// @ requires  sl.Bytes(p.buffer.UBuf(), 0, len(p.buffer.UBuf()))
// @ requires  acc(&p.d, R50) && acc(p.d.Mem(), _)
// @ requires  acc(&p.infoField, R20)
// @ requires  acc(&p.hopField, R20)
// pres for IO:
// @ requires  slayers.ValidPktMetaHdr(ubScionL) && p.scionLayer.EqAbsHeader(ubScionL)
// @ requires  absPkt(ubScionL).PathNotFullyTraversed()
// @ requires  p.EqAbsHopField(absPkt(ubScionL))
// @ preserves acc(&p.ingressID, R22)
// @ preserves acc(&p.mac, R20) && p.mac != nil && p.mac.Mem()
// @ preserves acc(&p.macBuffers.scionInput, R20)
// @ preserves sl.Bytes(p.macBuffers.scionInput, 0, len(p.macBuffers.scionInput))
// @ preserves acc(&p.cachedMac)
// @ preserves ubLL == nil || ubLL === ubScionL[startLL:endLL]
// @ preserves acc(&p.lastLayer, R55) && p.lastLayer != nil
// @ preserves &p.scionLayer !== p.lastLayer ==>
// @ 	acc(p.lastLayer.Mem(ubLL), R15)
// @ preserves &p.scionLayer === p.lastLayer ==>
// @ 	ubScionL === ubLL
// @ ensures   acc(&p.path, R20)
// @ ensures   acc(&p.infoField, R20)
// @ ensures   acc(&p.hopField,  R20)
// @ ensures   acc(&p.d, R50) && acc(p.d.Mem(), _)
// @ ensures   acc(p.scionLayer.Mem(ubScionL), R3)
// @ ensures   sl.Bytes(ubScionL, 0, len(ubScionL))
// @ ensures   p.d.validResult(respr, false)
// @ ensures   acc(&p.buffer, R50) && p.buffer != nil && p.buffer.Mem()
// @ ensures   sl.Bytes(p.buffer.UBuf(), 0, len(p.buffer.UBuf()))
// @ ensures   respr !== processResult{} ==>
// @ 	respr.OutPkt === p.buffer.UBuf()
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// @ ensures   reserr == nil ==>
// @ 	respr === processResult{}
// posts for IO:
// @ ensures   reserr == nil ==> old(p.DstIsLocalIngressID(ubScionL)) == p.DstIsLocalIngressID(ubScionL)
// @ ensures   reserr == nil ==> slayers.ValidPktMetaHdr(ubScionL) && p.scionLayer.EqAbsHeader(ubScionL)
// @ ensures   reserr == nil ==> absPkt(ubScionL).PathNotFullyTraversed()
// @ ensures   reserr == nil ==> old(p.LastHopLen(ubScionL)) == p.LastHopLen(ubScionL)
// @ ensures   reserr == nil ==>
// @ 	old(p.EqAbsInfoField(absPkt(ubScionL))) == p.EqAbsInfoField(absPkt(ubScionL))
// @ ensures   reserr == nil ==> p.EqAbsHopField(absPkt(ubScionL))
// @ ensures   reserr == nil ==> absPkt(ubScionL) == old(absPkt(ubScionL))
// @ ensures   reserr == nil ==> old(slayers.IsSupportedPkt(ubScionL)) == slayers.IsSupportedPkt(ubScionL)
// @ ensures   reserr != nil && respr.OutPkt != nil ==>
// @ 	absIO_val(respr.OutPkt, respr.EgressID).isIO_val_Unsupported
// @ decreases
func (p *slowPathPacketProcessor) handleSCMPTraceRouteRequest(ifID uint16 /*@, ghost ubScionL []byte, ghost ubLL []byte, ghost startLL int, ghost endLL int @*/) error {
	// @ ghost llIsScmp := false
	// @ ghost scionPldIsNil := false
	// @ ghost maybeStartPld := 0
	// @ ghost maybeEndPld := 0
	if p.lastLayer.NextLayerType() != slayers.LayerTypeSCMP {
		log.Debug("Packet with router alert, but not SCMP")
		// @ fold p.d.validResult(processResult{}, false)
		return nil
	}
	scionPld /*@ , start, end @*/ := p.lastLayer.LayerPayload( /*@ ubLL @*/ )
	// @ sl.SplitRange_Bytes(ubScionL, startLL, endLL, R1)
	// @ maybeStartPld = start
	// @ maybeEndPld = end
	// @ if scionPld == nil {
	// @ 	scionPldIsNil = true
	// @ 	sl.NilAcc_Bytes()
	// @ } else {
	// @ 	sl.SplitRange_Bytes(ubLL, start, end, R1)
	// @ }
	// @ gopacket.AssertInvariantNilDecodeFeedback()
	var scmpH /*@@@*/ slayers.SCMP
	// @ fold scmpH.NonInitMem()
	if err := scmpH.DecodeFromBytes(scionPld, gopacket.NilDecodeFeedback); err != nil {
		log.Debug("Parsing SCMP header of router alert", "err", err)
		// @ ghost if !scionPldIsNil { sl.CombineRange_Bytes(ubLL, start, end, R1) }
		// @ sl.CombineRange_Bytes(ubScionL, startLL, endLL, R1)
		// @ fold p.d.validResult(processResult{}, false)
		return nil
	}
	if /*@ (unfolding acc(scmpH.Mem(scionPld), R55) in @*/ scmpH.TypeCode /*@ ) @*/ != slayers.CreateSCMPTypeCode(slayers.SCMPTypeTracerouteRequest, 0) {
		log.Debug("Packet with router alert, but not traceroute request",
			"type_code", ( /*@ unfolding acc(scmpH.Mem(scionPld), R55) in @*/ scmpH.TypeCode))
		// @ ghost if !scionPldIsNil { sl.CombineRange_Bytes(ubLL, start, end, R1) }
		// @ sl.CombineRange_Bytes(ubScionL, startLL, endLL, R1)
		// @ fold p.d.validResult(processResult{}, false)
		return nil
	}
	var scmpP /*@@@*/ slayers.SCMPTraceroute
	// @ fold scmpP.NonInitMem()
	// @ unfold scmpH.Mem(scionPld)
	// @ unfold scmpH.BaseLayer.Mem(scionPld, 4)
	// @ sl.SplitRange_Bytes(scionPld, 4, len(scionPld), R1)
	if err := scmpP.DecodeFromBytes(scmpH.Payload, gopacket.NilDecodeFeedback); err != nil {
		log.Debug("Parsing SCMPTraceroute", "err", err)
		// @ ghost sl.CombineRange_Bytes(scionPld, 4, len(scionPld), R1)
		// @ ghost if !scionPldIsNil { sl.CombineRange_Bytes(ubLL, start, end, R1) }
		// @ sl.CombineRange_Bytes(ubScionL, startLL, endLL, R1)
		// @ fold p.d.validResult(processResult{}, false)
		return nil
	}
	// @ unfold scmpP.Mem(scmpH.Payload)
	// @ unfold scmpP.BaseLayer.Mem(scmpH.Payload, 4+addr.IABytes+slayers.scmpRawInterfaceLen)
	// @ p.d.getLocalIA()
	scmpP = slayers.SCMPTraceroute{
		Identifier: scmpP.Identifier,
		Sequence:   scmpP.Sequence,
		IA:         p.d.localIA,
		Interface:  uint64(ifID),
	}
	// @ ghost sl.CombineRange_Bytes(scionPld, 4, len(scionPld), R1)
	// @ ghost if !scionPldIsNil {
	// @ 	sl.CombineRange_Bytes(ubLL, maybeStartPld, maybeEndPld, R1)
	// @ }
	// @ sl.CombineRange_Bytes(ubScionL, startLL, endLL, R1)
	// @ ghost if tmpErr != nil && tmpRes.OutPkt != nil {
	// @ 	AbsUnsupportedPktIsUnsupportedVal(tmpRes.OutPkt, tmpRes.EgressID)
	// @ }	
	return p.packSCMP(slayers.SCMPTypeTracerouteReply, 0, &scmpP, false)
}

// @ requires  0 <= startLL && startLL <= endLL && endLL <= len(ubScionL)
// @ requires  acc(&p.path, R20)
// @ requires  sl.Bytes(ubScionL, 0, len(ubScionL))
// @ requires  acc(p.scionLayer.Mem(ubScionL), R3)
// @ requires  p.scionLayer.ValidPathMetaData(ubScionL)
// @ requires  p.path == p.scionLayer.GetPath(ubScionL)
// @ requires  acc(&p.buffer, R50) && p.buffer != nil && p.buffer.Mem()
// @ requires  sl.Bytes(p.buffer.UBuf(), 0, len(p.buffer.UBuf()))
// @ requires  acc(&p.d, R50) && acc(p.d.Mem(), _)
// @ preserves acc(&p.ingressID, R20)
// @ preserves ubLL == nil || ubLL === ubScionL[startLL:endLL]
// @ preserves acc(&p.lastLayer, R55) && p.lastLayer != nil
// @ preserves &p.scionLayer !== p.lastLayer ==>
// @ 	acc(p.lastLayer.Mem(ubLL), R15)
// @ preserves &p.scionLayer === p.lastLayer ==>
// @ 	ubScionL === ubLL
// @ ensures   acc(&p.d, R50) && acc(p.d.Mem(), _)
// @ ensures   acc(&p.path, R20)
// @ ensures   acc(p.scionLayer.Mem(ubScionL), R3)
// @ ensures   sl.Bytes(ubScionL, 0, len(ubScionL))
// @ ensures   p.d.validResult(respr, false)
// @ ensures   acc(&p.buffer, R50) && p.buffer != nil && p.buffer.Mem()
// @ ensures   sl.Bytes(p.buffer.UBuf(), 0, len(p.buffer.UBuf()))
// @ ensures   respr !== processResult{} ==>
// @ 	respr.OutPkt === p.buffer.UBuf()
// @ ensures   reserr == nil ==>
// @ 	int(p.scionLayer.GetPayloadLen(ubScionL)) == len(p.scionLayer.GetPayload(ubScionL))
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// @ ensures   reserr == nil ==>
// @ 	respr === processResult{}
// contracts for IO-spec
// @ requires  slayers.ValidPktMetaHdr(ubScionL) && p.scionLayer.EqAbsHeader(ubScionL)
// @ requires  absPkt(ubScionL).PathNotFullyTraversed()
// @ ensures   reserr == nil ==>
// @ 	slayers.ValidPktMetaHdr(ubScionL) && p.scionLayer.EqAbsHeader(ubScionL)
// @ ensures   reserr == nil ==> absPkt(ubScionL).PathNotFullyTraversed()
// @ ensures   reserr == nil ==> absPkt(ubScionL) == old(absPkt(ubScionL))
// @ ensures   reserr == nil ==> old(slayers.IsSupportedPkt(ubScionL)) == slayers.IsSupportedPkt(ubScionL)
// @ ensures   reserr != nil && respr.OutPkt != nil ==>
// @ 	absIO_val(respr.OutPkt, respr.EgressID).isIO_val_Unsupported
// @ decreases
func (p *scionPacketProcessor) validatePktLen( /*@ ghost ubScionL []byte, ghost ubLL []byte, ghost startLL int, ghost endLL int @*/ ) disposition {
	// @ unfold acc(p.scionLayer.Mem(ubScionL), R20)
	// @ defer fold acc(p.scionLayer.Mem(ubScionL), R20)
	if int(p.scionLayer.PayloadLen) == len(p.scionLayer.Payload) {
		// @ fold p.d.validResult(processResult{}, false)
		return pForward
	}
	log.Debug("SCMP response", "cause", badPacketSize, "header", p.scionLayer.PayloadLen,
		"actual", len(p.scionLayer.Payload))
	p.pkt.slowPathRequest = slowPathRequest{
		scmpType: slayers.SCMPTypeParameterProblem,
		code:     slayers.SCMPCodeInvalidPacketSize,
		pointer:  0,
	}
	// @ ghost if tmpErr != nil && tmpRes.OutPkt != nil {
	// @ 	AbsUnsupportedPktIsUnsupportedVal(tmpRes.OutPkt, tmpRes.EgressID)
	// @ }
	return pSlowPath
}

func (p *scionPacketProcessor) validateSrcHost() disposition {
	// We pay for this check only on the first hop.
	if p.scionLayer.SrcIA != p.d.localIA {
		return pForward
	}
	src, err := p.scionLayer.SrcAddr()
	if err == nil && src.IP().Is4In6() {
		err = unsupportedV4MappedV6Address
	}
	if err == nil {
		return pForward
	}

	log.Debug("SCMP response", "cause", err)
	p.pkt.slowPathRequest = slowPathRequest{
		scmpType: slayers.SCMPTypeParameterProblem,
		code:     slayers.SCMPCodeInvalidSourceAddress,
	}
	return pSlowPath
}

// @ requires  0 <= startLL && startLL <= endLL && endLL <= len(ub)
// @ requires  acc(&p.d, R5) && acc(p.d.Mem(), _) && p.d.WellConfigured()
// @ requires  p.d.getValSvc() != nil
// @ requires  acc(&p.rawPkt, R1) && ub === p.rawPkt
// @ requires  acc(&p.path, R10)
// @ requires  p.scionLayer.Mem(ub)
// @ requires  p.path == p.scionLayer.GetPath(ub)
// @ requires  sl.Bytes(ub, 0, len(ub))
// @ requires  acc(&p.ingressID, R15)
// @ requires  acc(&p.segmentChange) && !p.segmentChange
// @ requires  acc(&p.buffer, R10) && p.buffer != nil && p.buffer.Mem()
// @ requires  sl.Bytes(p.buffer.UBuf(), 0, len(p.buffer.UBuf()))
// @ preserves acc(&p.srcAddr, R10) && acc(p.srcAddr.Mem(), _)
// @ preserves acc(&p.lastLayer, R10)
// @ preserves p.lastLayer != nil
// @ preserves p.lastLayer !== &p.scionLayer ==>
// @ 	(llIsNil ==> acc(p.lastLayer.Mem(nil), R10)) &&
// @ 	(!llIsNil ==> acc(p.lastLayer.Mem(ub[startLL:endLL]), R10))
// @ preserves &p.scionLayer === p.lastLayer ==>
// @ 	!llIsNil && startLL == 0 && endLL == len(ub)
// @ preserves acc(&p.infoField)
// @ preserves acc(&p.hopField)
// @ preserves acc(&p.mac, R10) && p.mac != nil && p.mac.Mem()
// @ preserves acc(&p.macBuffers.scionInput, R10)
// @ preserves sl.Bytes(p.macBuffers.scionInput, 0, len(p.macBuffers.scionInput))
// @ preserves acc(&p.cachedMac)
// @ ensures   acc(&p.segmentChange)
// @ ensures   acc(&p.ingressID, R15)
// @ ensures   acc(&p.d, R5)
// @ ensures   acc(&p.path, R10)
// @ ensures   acc(&p.rawPkt, R1)
// @ ensures   acc(sl.Bytes(ub, 0, len(ub)), 1 - R15)
// @ ensures   p.d.validResult(respr, addrAliasesPkt)
// @ ensures   addrAliasesPkt ==> (
// @ 	respr.OutAddr != nil &&
// @ 	(acc(respr.OutAddr.Mem(), R15) --* acc(sl.Bytes(ub, 0, len(ub)), R15)))
// @ ensures   !addrAliasesPkt ==> acc(sl.Bytes(ub, 0, len(ub)), R15)
// @ ensures   acc(&p.buffer, R10) && p.buffer != nil && p.buffer.Mem()
// @ ensures   reserr == nil ==> p.scionLayer.Mem(ub)
// @ ensures   reserr != nil ==> p.scionLayer.NonInitMem()
// @ ensures   sl.Bytes(p.buffer.UBuf(), 0, len(p.buffer.UBuf()))
// @ ensures   respr.OutPkt != nil ==>
// @ 	(respr.OutPkt === ub || respr.OutPkt === p.buffer.UBuf())
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// contracts for IO-spec
// @ requires  p.d.DpAgreesWithSpec(dp)
// @ requires  dp.Valid()
// @ requires  p.scionLayer.EqAbsHeader(ub) && p.scionLayer.EqPathType(ub) && p.scionLayer.ValidScionInitSpec(ub)
// @ requires  acc(ioLock.LockP(), _)
// @ requires  ioLock.LockInv() == SharedInv!< dp, ioSharedArg !>
// @ requires  let absPkt := absIO_val(ub, p.ingressID) in
// @ 	absPkt.isIO_val_Pkt2 ==> ElemWitness(ioSharedArg.IBufY, path.ifsToIO_ifs(p.ingressID), absPkt.IO_val_Pkt2_2)
// @ ensures   reserr == nil && newAbsPkt.isIO_val_Pkt2 ==>
// @ 	ElemWitness(ioSharedArg.OBufY, newAbsPkt.IO_val_Pkt2_1, newAbsPkt.IO_val_Pkt2_2)
// @ ensures   respr.OutPkt != nil ==>
// @ 	newAbsPkt == absIO_val(respr.OutPkt, respr.EgressID)
// @ ensures   reserr != nil && respr.OutPkt != nil ==>
// @ 	newAbsPkt.isIO_val_Unsupported
// @ ensures (respr.OutPkt == nil) == (newAbsPkt == io.IO_val_Unit{})
// @ decreases 0 if sync.IgnoreBlockingForTermination()
// @ #backend[stateConsolidationMode(6)]
func (p *scionPacketProcessor) process(
// @ 	ghost ub []byte,
// @ 	ghost llIsNil bool,
// @ 	ghost startLL int,
// @ 	ghost endLL int,
// @ 	ghost ioLock gpointer[gsync.GhostMutex],
// @ 	ghost ioSharedArg SharedArg,
// @ 	ghost dp io.DataPlaneSpec,
) (dsp disposition /*@, ghost addrAliasesPkt bool, ghost newAbsPkt io.IO_val @*/) {
	// @ ghost ubLL := llIsNil ? ([]byte)(nil) : ub[startLL:endLL]
	if disp := p.parsePath( /*@ ub @*/ ); disp != pForward {
		// @ p.scionLayer.DowngradePerm(ub)
		return disp /*@, false, absReturnErr(r) @*/
	}
	if disp := p.determinePeer(); disp != pForward {
		// @ p.scionLayer.DowngradePerm(ub)
		return disp /*@, false, absReturnErr(r) @*/
	}
	// @ ghost var oldPkt io.IO_pkt2
	// @ ghost if(slayers.IsSupportedPkt(ub)) {
	// @ 	absIO_valLemma(ub, p.ingressID)
	// @ 	oldPkt = absIO_val(ub, p.ingressID).IO_val_Pkt2_2
	// @ } else {
	// @ 	absPktFutureLemma(ub)
	// @ 	oldPkt = absPkt(ub)
	// @ }
	// @ nextPkt := oldPkt
	if disp := p.validateHopExpiry( /*@ ub, ubLL, startLL, endLL @*/ ); disp != pForward {
		// @ p.scionLayer.DowngradePerm(ub)
		return disp /*@, false, absReturnErr(r) @*/
	}
	if disp := p.validateIngressID( /*@ ub, ubLL, startLL, endLL @*/ ); disp != pForward {
		// @ p.scionLayer.DowngradePerm(ub)
		return disp /*@, false, absReturnErr(r) @*/
	}
	// @ assert AbsValidateIngressIDConstraint(nextPkt, path.ifsToIO_ifs(p.ingressID))
	if disp := p.validatePktLen( /*@ ub, ubLL, startLL, endLL @*/ ); disp != pForward {
		// @ p.scionLayer.DowngradePerm(ub)
		return disp /*@, false, absReturnErr(r) @*/
	}
	if disp := p.validateTransitUnderlaySrc( /*@ ub @*/ ); disp != pForward {
		// @ p.scionLayer.DowngradePerm(ub)
		return disp /*@, false, absReturnErr(r) @*/
	}
	if disp := p.validateSrcDstIA( /*@ ub, ubLL, startLL, endLL @*/ ); disp != pForward {
		// @ p.scionLayer.DowngradePerm(ub)
		return disp /*@, false, absReturnErr(r) @*/
	}
	if disp := p.validateSrcHost(); disp != pForward {
		// @ p.scionLayer.DowngradePerm(ub)
		return disp /*@, false, absReturnErr(r) @*/
	}
	if disp := p.updateNonConsDirIngressSegID( /*@ ub @*/ ); disp != pForward {
		// @ p.scionLayer.DowngradePerm(ub)
		return disp
	}
	// @ assert absPkt(ub) == AbsUpdateNonConsDirIngressSegID(oldPkt, path.ifsToIO_ifs(p.ingressID))
	// @ nextPkt = absPkt(ub)
	// @ AbsValidateIngressIDLemma(oldPkt, nextPkt, path.ifsToIO_ifs(p.ingressID))
	if disp := p.verifyCurrentMAC( /*@ dp, ub, ubLL, startLL, endLL @*/ ); disp != pForward {
		// @ p.scionLayer.DowngradePerm(ub)
		return disp /*@, false, absReturnErr(r) @*/
	}
	// @ assert AbsVerifyCurrentMACConstraint(nextPkt, dp)
	if disp := p.handleIngressRouterAlert( /*@ ub, ubLL, startLL, endLL @*/ ); disp != pForward {
		// @ p.scionLayer.DowngradePerm(ub)
		return disp /*@, false, absReturnErr(r) @*/
	}
	// @ assert nextPkt == absPkt(ub)
	// Inbound: pkts destined to the local IA.
	// @ p.d.getLocalIA()
	if /*@ unfolding acc(p.scionLayer.Mem(ub), R50) in (unfolding acc(p.scionLayer.HeaderMem(ub[slayers.CmnHdrLen:]), R55) in @*/ p.scionLayer.DstIA /*@ ) @*/ == p.d.localIA {
		// @ assert p.DstIsLocalIngressID(ub)
		// @ assert unfolding acc(p.scionLayer.Mem(ub), R50) in
		// @ 	(unfolding acc(p.scionLayer.HeaderMem(ub[slayers.CmnHdrLen:]), R55) in
		// @ 	p.scionLayer.DstIA) == p.d.localIA
		// @ p.LocalDstLemma(ub)
		// @ assert p.ingressID != 0
		// @ assert len(nextPkt.CurrSeg.Future) == 1
		disp  /*@, aliasesUb @*/ := p.resolveInbound( /*@ ub, ubLL, startLL, endLL @*/ )
		if disp != pForward {
			// @ p.scionLayer.DowngradePerm(ub)
			return disp /*@, aliasesUb, absReturnErr(r) @*/
		}
		p.pkt.trafficType = ttIn
		return pForward /*@, aliasesUb, newAbsPkt @*/
	}

	// Outbound: pkt leaving the local IA. This Could be:
	// * Pure outbound: from this AS, in via internal, out via external.
	// * ASTransit in: from another AS, in via external, out via internal to other BR.
	// * ASTransit out: from another AS, in via internal from other BR, out via external.
	// * BRTransit: from another AS, in via external, out via external.
	// @ unfold acc(p.scionLayer.Mem(ub), R3)
	// @ ghost ubPath := p.scionLayer.UBPath(ub)
	if p.path.IsXover( /*@ ubPath @*/ ) && !p.peering {
		// An effective cross-over is a change of segment other than at
		// a peering hop.
		// @ assert p.GetIsXoverSpec(ub)
		// @ ghost currBase := p.path.GetBase(ubPath)
		// @ fold acc(p.scionLayer.Mem(ub), R3)
		if disp := p.doXover( /*@ ub, currBase @*/ ); disp != pForward {
			// @ fold p.d.validResult(processResult{}, false)
			return disp /*@, false, absReturnErr(r) @*/
		}
		// doXover() has changed the current segment and hop field.
		// We need to validate the new hop field.
		// @ assert absPkt(ub) == AbsDoXover(nextPkt)
		// @ AbsValidateIngressIDXoverLemma(nextPkt, AbsDoXover(nextPkt), path.ifsToIO_ifs(p.ingressID))
		// @ nextPkt = absPkt(ub)
		if disp := p.validateHopExpiry( /*@ ub, ubLL, startLL, endLL @*/ ); disp != pForward {
			// @ p.scionLayer.DowngradePerm(ub)
			return disp /*@, false, absReturnErr(r) @*/
		}
		// verify the new block
		if disp := p.verifyCurrentMAC( /*@ dp, ub, ubLL, startLL, endLL @*/ ); disp != pForward {
			// @ p.scionLayer.DowngradePerm(ub)
			return disp /*@, false, absReturnErr(r) @*/
		}
		// @ assert AbsVerifyCurrentMACConstraint(nextPkt, dp)
		// @ unfold acc(p.scionLayer.Mem(ub), R3)
	}

	// Assign egress interface to the packet early. ICMP responses, if we make any, will need this.
	// Even if the egress interface is not valid, it can be useful in SCMP reporting.
	// @ assert nextPkt == absPkt(ub)
	egressID := p.egressInterface( /*@ nextPkt @*/ )
	p.pkt.egress = egressID

	// @ assert p.path.GetBase(ubPath).Valid()
	// @ p.path.GetBase(ubPath).NotIsXoverAfterIncPath()
	// @ fold acc(p.scionLayer.Mem(ub), R3)
	// @ assert p.segmentChange ==> nextPkt.RightSeg != none[io.IO_seg2]
	if disp := p.validateEgressID( /*@ dp, ub, ubLL, startLL, endLL @*/ ); disp != pForward {
		// @ p.scionLayer.DowngradePerm(ub)
		return disp /*@, false, absReturnErr(r) @*/
	}

	// @ assert !p.segmentChange ==> AbsValidateEgressIDConstraint(nextPkt, (p.ingressID != 0), dp)
	// @ assert p.segmentChange ==> p.ingressID != 0 && AbsValidateEgressIDConstraintXover(nextPkt, dp)
	// handle egress router alert before we check if it's up because we want to
	// send the reply anyway, so that trace route can pinpoint the exact link
	// that failed.
	if disp := p.handleEgressRouterAlert( /*@ ub, ubLL, startLL, endLL @*/ ); disp != pForward {
		// @ p.scionLayer.DowngradePerm(ub)
		return disp /*@, false, absReturnErr(r) @*/
	}
	// @ assert nextPkt == absPkt(ub)
	if disp := p.validateEgressUp( /*@ ub, ubLL, startLL, endLL @*/ ); disp != pForward {
		// @ p.scionLayer.DowngradePerm(ub)
		return disp /*@, false, absReturnErr(r) @*/
	}
	// @ assert AbsEgressInterfaceConstraint(nextPkt, path.ifsToIO_ifs(egressID))
	// @ p.d.getExternalMem()
	// @ if p.d.external != nil { unfold acc(accBatchConn(p.d.external), _) }
	if _, ok := p.d.external[egressID]; ok {
		// @ p.d.getDomExternalLemma()
		// @ p.d.EgressIDNotZeroLemma(egressID, dp)
		// Not ASTransit in
		if disp := p.processEgress(); disp != pForward {
			return disp /*@, false, absReturnErr(processResult{}) @*/
		}
		// Finish deciding the trafficType...
		var tt trafficType
		if p.scionLayer.SrcIA == p.d.localIA {
			// Pure outbound
			tt = ttOut
		} else if p.pkt.ingress == 0 {
			// ASTransit out
			tt = ttOutTransit
		} else {
			// Therefore it is BRTransit
			tt = ttBrTransit
		}
		p.pkt.trafficType = tt
		// @ p.d.InDomainExternalInForwardingMetrics(egressID)
		// @ assert absPkt(ub) == AbsProcessEgress(nextPkt)
		// @ nextPkt = absPkt(ub)
		// @ ghost if(slayers.IsSupportedPkt(ub)) {
		// @ 	ghost if(!p.segmentChange) {
		// @ 		ExternalEnterOrExitEvent(oldPkt, path.ifsToIO_ifs(p.ingressID), nextPkt, path.ifsToIO_ifs(egressID), ioLock, ioSharedArg, dp)
		// @ 	} else {
		// @ 		XoverEvent(oldPkt, path.ifsToIO_ifs(p.ingressID), nextPkt, path.ifsToIO_ifs(egressID), ioLock, ioSharedArg, dp)
		// @ 	}
		// @ }
		// @ newAbsPkt = reveal absIO_val(p.rawPkt, egressID)
		// @ fold p.d.validResult(processResult{EgressID: egressID, OutConn: c, OutPkt: p.rawPkt}, false)
		return pForward /*@, false, newAbsPkt @*/
	}

	// ASTransit in: pkt leaving this AS through another BR.
	// @ p.d.getDomExternalLemma()
	// @ p.IngressIDNotZeroLemma(nextPkt, egressID)
	// @ p.d.getInternalNextHops()
	// @ ghost if p.d.internalNextHops != nil { unfold acc(accAddr(p.d.internalNextHops), _) }
	if a, ok := p.d.internalNextHops[egressID]; ok {
		// @ p.d.getInternal()
		// @ ghost if(slayers.IsSupportedPkt(ub)) {
		// @ 	if(!p.segmentChange) {
		// @ 		InternalEnterEvent(oldPkt, path.ifsToIO_ifs(p.ingressID), nextPkt, none[io.IO_ifs], ioLock, ioSharedArg, dp)
		// @ 	} else {
		// @ 		XoverEvent(oldPkt, path.ifsToIO_ifs(p.ingressID), nextPkt, none[io.IO_ifs], ioLock, ioSharedArg, dp)
		// @ 	}
		// @ }
		// @ newAbsPkt = reveal absIO_val(p.rawPkt, 0)
		// @ fold p.d.validResult(processResult{OutConn: p.d.internal, OutAddr: a, OutPkt: p.rawPkt}, false)

		p.pkt.trafficType = ttInTransit
		updateNetAddrFromAddrPort(p.pkt.dstAddr, a)
		// The packet must go to the other router via the internal interface.
		p.pkt.egress = 0
		return pForward /*@, false, newAbsPkt @*/
	}

	errCode := slayers.SCMPCodeUnknownHopFieldEgress
	if !p.infoField.ConsDir {
		errCode = slayers.SCMPCodeUnknownHopFieldIngress
	}
	// @ establishCannotRoute()
	log.Debug("SCMP response", "cause", cannotRoute)
	p.pkt.slowPathRequest = slowPathRequest{
		scmpType: slayers.SCMPTypeParameterProblem,
		code:     errCode,
		pointer:  p.currentHopPointer(),
	}
	return pSlowPath
}

// @ requires  acc(&p.rawPkt, R15)
// @ requires  p.scionLayer.Mem(p.rawPkt)
// @ requires  acc(&p.ingressID,  R15)
// @ requires  acc(&p.d, R15) && acc(p.d.Mem(), _) && p.d.WellConfigured()
// @ requires  p.d.getValSvc() != nil
// @ requires  sl.Bytes(p.rawPkt, 0, len(p.rawPkt))
// @ preserves acc(&p.mac, R10)
// @ preserves p.mac != nil && p.mac.Mem()
// @ preserves acc(&p.macBuffers.scionInput, R10)
// @ preserves sl.Bytes(p.macBuffers.scionInput, 0, len(p.macBuffers.scionInput))
// @ preserves acc(&p.buffer, R10) && p.buffer != nil && p.buffer.Mem()
// @ preserves sl.Bytes(p.buffer.UBuf(), 0, len(p.buffer.UBuf()))
// @ ensures   acc(&p.rawPkt, R15)
// @ ensures   p.scionLayer.Mem(p.rawPkt)
// @ ensures   acc(&p.ingressID,  R15)
// @ ensures   acc(&p.d,          R15)
// @ ensures   p.d.validResult(respr, addrAliasesPkt)
// @ ensures   acc(sl.Bytes(p.rawPkt, 0, len(p.rawPkt)), 1 - R15)
// @ ensures   addrAliasesPkt ==> (
// @ 	respr.OutAddr != nil &&
// @ 	let rawPkt := p.rawPkt in
// @ 	(acc(respr.OutAddr.Mem(), R15) --* acc(sl.Bytes(rawPkt, 0, len(rawPkt)), R15)))
// @ ensures  !addrAliasesPkt ==> acc(sl.Bytes(p.rawPkt, 0, len(p.rawPkt)), R15)
// @ ensures  respr.OutPkt != nil ==> respr.OutPkt === p.rawPkt
// @ ensures  reserr != nil ==> reserr.ErrorMem()
// contracts for IO-spec
// @ requires p.scionLayer.EqPathType(p.rawPkt)
// @ requires !slayers.IsSupportedPkt(p.rawPkt)
// @ ensures  (respr.OutPkt == nil) == (newAbsPkt == io.IO_val_Unit{})
// @ ensures  respr.OutPkt != nil ==>
// @ 	newAbsPkt == absIO_val(respr.OutPkt, respr.EgressID) &&
// @ 	newAbsPkt.isIO_val_Unsupported
// @ decreases 0 if sync.IgnoreBlockingForTermination()
func (p *scionPacketProcessor) processOHP() (dsp disposition /*@ , ghost addrAliasesPkt bool, ghost newAbsPkt io.IO_val @*/) {
	// @ ghost ubScionL := p.rawPkt
	// @ p.scionLayer.ExtractAcc(ubScionL)
	s := p.scionLayer
	// @ ghost  ubPath := p.scionLayer.UBPath(ubScionL)
	// @ unfold acc(p.scionLayer.Mem(ubScionL), R15)
	// @ defer fold acc(p.scionLayer.Mem(ubScionL), R15)
	// @ apply acc(&p.scionLayer, R16) --* acc(p.scionLayer.Mem(ubScionL), R15)
	// @ assert s.Path === p.scionLayer.Path
	ohp, ok := s.Path.(*onehop.Path)
	if !ok {
		// TODO parameter problem -> invalid path
		// @ establishMemMalformedPath()
		// @ fold p.d.validResult(processResult{}, false)
		return errorDiscard("error", malformedPath)
	}
	if /*@ unfolding acc(s.Path.Mem(ubPath), R50) in @*/ !ohp.Info.ConsDir {
		// TODO parameter problem -> invalid path
		// @ establishMemMalformedPath()
		// @ fold p.d.validResult(processResult{}, false)
		return errorDiscard("error", malformedPath)
	}

	// OHP leaving our IA
	if p.ingressID == 0 {
		// @ p.d.getLocalIA()
		if !p.d.localIA.Equal(s.SrcIA) {
			// @ establishCannotRoute()
			// TODO parameter problem -> invalid path
			// @ fold p.d.validResult(processResult{}, false)
			return errorDiscard("error", cannotRoute)
		}
		// @ p.d.getNeighborIAs()
		neighborIA, ok := p.d.neighborIAs[ /*@ unfolding acc(ohp.Mem(ubPath), R50) in (unfolding acc(ohp.FirstHop.Mem(), R55) in @*/ ohp.FirstHop.ConsEgress /*@ ) @*/]
		if !ok {
			// @ establishCannotRoute()
			// TODO parameter problem invalid interface
			return errorDiscard("error", cannotRoute)
		}
		if !neighborIA.Equal(s.DstIA) {
			// @ establishCannotRoute()
			return errorDiscard("error", cannotRoute)
		}
		// @ unfold acc(ohp.Mem(ubPath), R50)
		// @ defer fold acc(ohp.Mem(ubPath), R50)
		// @ unfold acc(ohp.FirstHop.Mem(), R54)
		// @ defer fold acc(ohp.FirstHop.Mem(), R54)
		// @ preserves acc(&ohp.Info, R55) && acc(&ohp.FirstHop, R55)
		// @ preserves acc(&p.macBuffers.scionInput, R55)
		// @ preserves acc(&p.mac, R55) && p.mac != nil && p.mac.Mem()
		// @ preserves sl.Bytes(p.macBuffers.scionInput, 0, len(p.macBuffers.scionInput))
		// @ decreases
		// @ outline (
		mac  /*@@@*/ := path.MAC(p.mac, ohp.Info, ohp.FirstHop, p.macInputBuffer[:path.MACBufferSize])
		// (VerifiedSCION) introduced separate copy to avoid exposing quantified permissions outside the scope of this outline block.
		macCopy := mac
		// @ fold acc(sl.Bytes(ohp.FirstHop.Mac[:], 0, len(ohp.FirstHop.Mac[:])), R56)
		// @ fold acc(sl.Bytes(mac[:], 0, len(mac)), R56)
		compRes := subtle.ConstantTimeCompare(ohp.FirstHop.Mac[:], mac[:]) == 0
		// @ unfold acc(sl.Bytes(ohp.FirstHop.Mac[:], 0, len(ohp.FirstHop.Mac[:])), R56)
		// @ )		
		if compRes {
			// TODO parameter problem -> invalid MAC
			return errorDiscard("error", macVerificationFailed)
		}
		// @ assert reveal p.scionLayer.EqPathType(p.rawPkt)
		// @ unfold acc(p.scionLayer.Mem(ubScionL), 1-R15)
		// @ unfold acc(s.Path.Mem(ubPath), 1-R50)
		ohp.Info.UpdateSegID(ohp.FirstHop.Mac /*@, ohp.FirstHop.ToIO_HF() @*/)
		// @ fold acc(s.Path.Mem(ubPath), 1-R50)
		// @ fold acc(p.scionLayer.Mem(ubScionL), 1-R15)
		// @ assert reveal p.scionLayer.EqPathType(p.rawPkt)

		if err := updateSCIONLayer(p.pkt.rawPacket, s, p.buffer); err != nil {
			return errorDiscard("error", err)
		}
		p.pkt.egress = ohp.FirstHop.ConsEgress
		return pForward
	}
	// OHP entering our IA
	// @ p.d.getLocalIA()
	if !p.d.localIA.Equal(s.DstIA) {
		// @ establishCannotRoute()
		return errorDiscard("error", cannotRoute)
	}
	// @ p.d.getNeighborIAs()
	neighborIA := p.d.neighborIAs[p.pkt.ingress]
	if !neighborIA.Equal(s.SrcIA) {
		// @ establishCannotRoute()
		return errorDiscard("error", cannotRoute)
}
	// @ assert reveal p.scionLayer.EqPathType(p.rawPkt)
	// @ unfold acc(p.scionLayer.Mem(ubScionL), 1-R15)
	// @ unfold s.Path.Mem(ubPath)
	// @ unfold ohp.SecondHop.Mem()
	ohp.SecondHop = path.HopField{
		ConsIngress: p.pkt.ingress,
		ExpTime:/*@ unfolding acc(ohp.FirstHop.Mem(), R55) in @*/ ohp.FirstHop.ExpTime,
	}
	// (VerifiedSCION) the following property follows from the type system, but
	// Gobra cannot prove it yet.
	// @ assume 0 <= p.ingressID
	// XXX(roosd): Here we leak the buffer into the SCION packet header.
	// This is okay because we do not operate on the buffer or the packet
	// for the rest of processing.

	ohp.SecondHop.Mac = path.MAC(p.mac, ohp.Info, ohp.SecondHop,
		p.macInputBuffer[:path.MACBufferSize])
	// @ fold ohp.SecondHop.Mem()
	// @ fold s.Path.Mem(ubPath)
	// @ fold acc(p.scionLayer.Mem(ubScionL), 1-R15)
	// @ assert reveal p.scionLayer.EqPathType(p.rawPkt)
	
	// (VerifiedSCION) the second parameter was changed from 's' to 'p.scionLayer' due to the
	// changes made to 'updateSCIONLayer'.
	if err := updateSCIONLayer(p.pkt.rawPacket, s, p.buffer); err != nil {
		// @ fold p.d.validResult(processResult{}, false)
		return errorDiscard("error", err)
	}

	// (VerifiedSCION) the parameter was changed from 's' to '&p.scionLayer' due to the
	// changes made to 'resolveLocalDst'.
	err := p.d.resolveLocalDst(p.pkt.dstAddr, s, p.lastLayer)
	if err != nil {
		// @ ghost if addrAliases {
		// @ 	apply acc(a.Mem(), R15) --* acc(sl.Bytes(ubScionL, 0, len(ubScionL)), R15)
		// @ }
		return errorDiscard("error", err)
	}
	// @ p.d.getInternal()
	// @ assert p.d.internal != nil ==> acc(p.d.internal.Mem(), _)
	return pForward
}

// @ requires  acc(d.Mem(), _)
// @ requires  d.getValSvc() != nil
// @ requires  acc(sl.Bytes(ub, 0, len(ub)), R15)
// @ preserves acc(s.Mem(ub), R14)
// @ ensures   !addrAliasesUb ==> acc(sl.Bytes(ub, 0, len(ub)), R15)
// @ ensures   !addrAliasesUb && resaddr != nil ==> acc(resaddr.Mem(), _)
// @ ensures   addrAliasesUb ==> resaddr != nil
// @ ensures   addrAliasesUb ==> acc(resaddr.Mem(), R15)
// @ ensures   addrAliasesUb ==> (acc(resaddr.Mem(), R15) --* acc(sl.Bytes(ub, 0, len(ub)), R15))
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// (VerifiedSCION) the type of 's' was changed from slayers.SCION to *slayers.SCION. This makes
// specs a lot easier and, makes the implementation faster as well by avoiding passing large data-structures
// by value. We should consider porting merging this in upstream SCION.
// @ decreases 0 if sync.IgnoreBlockingForTermination()
func (d *DataPlane) resolveLocalDst(
	resolvedDst *net.UDPAddr,
	s slayers.SCION,
	lastLayer gopacket.DecodingLayer,
) error {
	// @ ghost start, end := s.ExtractAcc(ub)
	// @ assert s.RawDstAddr === ub[start:end]
	// @ sl.SplitRange_Bytes(ub, start, end, R15)
	// @ assert acc(sl.Bytes(s.RawDstAddr, 0, len(s.RawDstAddr)), R15)
	dst, err := s.DstAddr()
	// @ apply acc(s, R16) --* acc(s.Mem(ub), R15)
	if err != nil {
		// @ sl.CombineRange_Bytes(ub, start, end, R15)
		return invalidDstAddr
	}
	switch dst.Type() {
	case addr.HostTypeSVC:
		// For map lookup use the Base address, i.e. strip the multi cast
		// information, because we only register base addresses in the map.
		// @ d.getSvcMem()
		a, ok := d.svc.Any(dst.SVC().Base())
		if !ok {
			// @ apply acc(dst.Mem(), R15) --* acc(sl.Bytes(ub[start:end], 0, len(ub[start:end])), R15)
			// @ sl.CombineRange_Bytes(ub, start, end, R15)
			// @ establishNoSVCBackend()
			return noSVCBackend
		}
		// if SVC address is outside the configured port range we send to the fix
		// port.
		if a.Port() < d.dispatchedPortStart || a.Port() > d.dispatchedPortEnd {
			updateNetAddrFromAddrAndPort(resolvedDst, a.Addr(), topology.EndhostPort)
		} else {
			updateNetAddrFromAddrPort(resolvedDst, a)
		}
		// @ apply acc(dst.Mem(), R15) --* acc(sl.Bytes(ub[start:end], 0, len(ub[start:end])), R15)
		// @ sl.CombineRange_Bytes(ub, start, end, R15)
		return nil
	case addr.HostTypeIP:
		// Parse UPD port and rewrite underlay IP/UDP port
		// TODO(jiceatscion): IP() is returned by value. The cost of copies adds up.
		dstIP := dst.IP()
		if dstIP.Is4In6() {
			return unsupportedV4MappedV6Address
		}
		// Zero IP addresses (per IsUnspecified()) are not supported. Zero valued netip.Addr objects
		// (per IsInvalid()) cannot happen here as dstIP is initialized from packet header data.
		if dstIP.IsUnspecified() {
			return unsupportedUnspecifiedAddress
		}
		return d.addEndhostPort(resolvedDst, lastLayer, dstIP)
	default:
		panic("unexpected address type returned from DstAddr")
	}
}

// @ requires acc(dst.Mem(), R15)
// @ ensures  res != nil && acc(res.Mem(), R15)
// @ ensures  acc(res.Mem(), R15) --* acc(dst.Mem(), R15)
// @ decreases
func (d *DataPlane) addEndhostPort(
	resolvedDst *net.UDPAddr,
	lastLayer gopacket.DecodingLayer,
	dst netip.Addr,
) error {

	// Parse UPD port and rewrite underlay IP/UDP port
	l4Type := nextHdr(lastLayer)
	port := uint16(topology.EndhostPort)

	switch l4Type {
	case slayers.L4UDP:
		if len(lastLayer.LayerPayload()) < 8 {
			// TODO(JordiSubira): Treat this as a parameter problem
			return serrors.New("SCION/UDP header len too small", "length",
				len(lastLayer.LayerPayload()))
		}
		port = binary.BigEndian.Uint16(lastLayer.LayerPayload()[2:])
		if port < d.dispatchedPortStart || port > d.dispatchedPortEnd {
			port = topology.EndhostPort
		}
	case slayers.L4SCMP:
		var scmpLayer slayers.SCMP
		err := scmpLayer.DecodeFromBytes(lastLayer.LayerPayload(), gopacket.NilDecodeFeedback)
		if err != nil {
			// TODO(JordiSubira): Treat this as a parameter problem.
			return serrors.Wrap("decoding SCMP layer for extracting endhost dst port", err)
		}
		port, err = getDstPortSCMP(&scmpLayer)
		if err != nil {
			// TODO(JordiSubira): Treat this as a parameter problem.
			return serrors.Wrap("getting dst port from SCMP message", err)
		}
		// if the SCMP dst port is outside the range, we send it to the EndhostPort
		if port < d.dispatchedPortStart || port > d.dispatchedPortEnd {
			port = topology.EndhostPort
		}
	default:
		log.Debug("msg", "protocol", l4Type)
	}
	updateNetAddrFromAddrAndPort(resolvedDst, dst, port)
	return nil
}

func getDstPortSCMP(scmp *slayers.SCMP) (uint16, error) {
	// XXX(JordiSubira): This implementation is far too slow for the dataplane.
	// We should reimplement this with fewer helpers and memory allocations, since
	// our sole goal is to parse the L4 port or identifier in the offending packets.
	if scmp.TypeCode.Type() == slayers.SCMPTypeEchoRequest ||
		scmp.TypeCode.Type() == slayers.SCMPTypeTracerouteRequest {
		return topology.EndhostPort, nil
	}
	if scmp.TypeCode.Type() == slayers.SCMPTypeEchoReply {
		var scmpEcho slayers.SCMPEcho
		err := scmpEcho.DecodeFromBytes(scmp.Payload, gopacket.NilDecodeFeedback)
		if err != nil {
			return 0, err
		}
		return scmpEcho.Identifier, nil
	}
	if scmp.TypeCode.Type() == slayers.SCMPTypeTracerouteReply {
		var scmpTraceroute slayers.SCMPTraceroute
		err := scmpTraceroute.DecodeFromBytes(scmp.Payload, gopacket.NilDecodeFeedback)
		if err != nil {
			return 0, err
		}
		return scmpTraceroute.Identifier, nil
	}

	// Drop unknown SCMP error messages.
	if scmp.NextLayerType() == gopacket.LayerTypePayload {
		return 0, serrors.New("unsupported SCMP error message",
			"type", scmp.TypeCode.Type())
	}
	l, err := decodeSCMP(scmp)
	if err != nil {
		return 0, err
	}
	if len(l) != 2 {
		return 0, serrors.New("SCMP error message without payload")
	}
	gpkt := gopacket.NewPacket(*l[1].(*gopacket.Payload), slayers.LayerTypeSCION,
		gopacket.DecodeOptions{
			NoCopy: true,
		},
	)

	// If the offending packet was UDP/SCION, use the source port to deliver.
	if udp := gpkt.Layer(slayers.LayerTypeSCIONUDP); udp != nil {
		port := udp.(*slayers.UDP).SrcPort
		// XXX(roosd): We assume that the zero value means the UDP header is
		// truncated. This flags packets of misbehaving senders as truncated, if
		// they set the source port to 0. But there is no harm, since those
		// packets are destined to be dropped anyway.
		if port == 0 {
			return 0, serrors.New("SCMP error with truncated UDP header")
		}
		return port, nil
	}

	// If the offending packet was SCMP/SCION, and it is an echo or traceroute,
	// use the Identifier to deliver. In all other cases, the message is dropped.
	if scmp := gpkt.Layer(slayers.LayerTypeSCMP); scmp != nil {

		tc := scmp.(*slayers.SCMP).TypeCode
		// SCMP Error messages in response to an SCMP error message are not allowed.
		if !tc.InfoMsg() {
			return 0, serrors.New("SCMP error message in response to SCMP error message",
				"type", tc.Type())
		}
		// We only support echo and traceroute requests.
		t := tc.Type()
		if t != slayers.SCMPTypeEchoRequest && t != slayers.SCMPTypeTracerouteRequest {
			return 0, serrors.New("unsupported SCMP info message", "type", t)
		}

		var port uint16
		// Extract the port from the echo or traceroute ID field.
		if echo := gpkt.Layer(slayers.LayerTypeSCMPEcho); echo != nil {
			port = echo.(*slayers.SCMPEcho).Identifier
		} else if tr := gpkt.Layer(slayers.LayerTypeSCMPTraceroute); tr != nil {
			port = tr.(*slayers.SCMPTraceroute).Identifier
		} else {
			return 0, serrors.New("SCMP error with truncated payload")
		}
		return port, nil
	}
	return 0, serrors.New("unknown SCION SCMP content")
}

// decodeSCMP decodes the SCMP payload. WARNING: Decoding is done with NoCopy set.
func decodeSCMP(scmp *slayers.SCMP) ([]gopacket.SerializableLayer, error) {
	gpkt := gopacket.NewPacket(scmp.Payload, scmp.NextLayerType(),
		gopacket.DecodeOptions{NoCopy: true})
	layers := gpkt.Layers()
	if len(layers) == 0 || len(layers) > 2 {
		return nil, serrors.New("invalid number of SCMP layers", "count", len(layers))
	}
	ret := make([]gopacket.SerializableLayer, len(layers))
	for i, l := range layers {
		s, ok := l.(gopacket.SerializableLayer)
		if !ok {
			return nil, serrors.New("invalid SCMP layer, not serializable", "index", i)
		}
		ret[i] = s
	}
	return ret, nil
}

// TODO(matzf) this function is now only used to update the OneHop-path.
// This should be changed so that the OneHop-path can be updated in-place, like
// the scion.Raw path.
// @ requires  acc(s.Mem(rawPkt), R00)
// @ requires  s.HasOneHopPath(rawPkt)
// @ requires  sl.Bytes(rawPkt, 0, len(rawPkt))
// @ preserves buffer != nil && buffer.Mem()
// @ preserves sl.Bytes(buffer.UBuf(), 0, len(buffer.UBuf()))
// pres for IO:
// @ requires s.EqPathType(rawPkt)
// @ requires !slayers.IsSupportedPkt(rawPkt)
// @ ensures   sl.Bytes(rawPkt, 0, len(rawPkt))
// @ ensures   acc(s.Mem(rawPkt), R00)
// @ ensures   res != nil ==> res.ErrorMem()
// post for IO:
// @ ensures res == nil ==> !slayers.IsSupportedPkt(rawPkt)
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
	// @ reveal slayers.IsSupportedRawPkt(buffer.View())
	// TODO(lukedirtwalker): We should add a method to the scion layers
	// which can write into the existing buffer, see also the discussion in
	// https://fsnets.slack.com/archives/C8ADBBG0J/p1592805884250700
	rawContents := buffer.Bytes()
	// @ assert !(reveal slayers.IsSupportedPkt(rawContents))
	// @ s.InferSizeOHP(rawPkt)
	// @ assert len(rawContents) <= len(rawPkt)
	// @ unfold sl.Bytes(rawPkt, 0, len(rawPkt))
	// @ unfold acc(sl.Bytes(rawContents, 0, len(rawContents)), R20)
	// (VerifiedSCION) proving that the reslicing operation below is safe
	// was tricky and required enriching (non-modularly) the invariants of *onehop.Path
	// and *slayers.SCION.
	// @ assert forall i int :: { &rawPkt[:len(rawContents)][i] }{ &rawPkt[i] } 0 <= i && i < len(rawContents) ==>
	// @ 	 &rawPkt[i] == &rawPkt[:len(rawContents)][i]
	copy(rawPkt[:len(rawContents)], rawContents /*@ , R20 @*/)
	// @ fold sl.Bytes(rawPkt, 0, len(rawPkt))
	// @ fold acc(sl.Bytes(rawContents, 0, len(rawContents)), R20)
	// @ assert !(reveal slayers.IsSupportedPkt(rawPkt))
	return nil
}

type bfdSend struct {
	conn             BatchConn
	srcAddr, dstAddr netip.AddrPort
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
func newBFDSend(conn BatchConn, srcIA, dstIA addr.IA, srcAddr, dstAddr netip.AddrPort,
	ifID uint16, mac hash.Hash) (*bfdSend, error) {

	scn := &slayers.SCION{
		Version:      0,
		TrafficClass: 0xb8,
		FlowID:       0xdead,
		NextHdr:      slayers.L4BFD,
		SrcIA:        srcIA,
		DstIA:        dstIA,
	}

	if !srcAddr.IsValid() {
		return nil, serrors.New("invalid source IP", "ip", srcAddr)
	}
	if !dstAddr.IsValid() {
		return nil, serrors.New("invalid source IP", "ip", srcAddr)
	}

	srcAddrIP := srcAddr.Addr()
	dstAddrIP := dstAddr.Addr()
	if err := scn.SetSrcAddr(addr.HostIP(srcAddrIP) /*@ , false @*/); err != nil {
		panic(err) // Must work
	}
	if err := scn.SetDstAddr(addr.HostIP(dstAddrIP) /*@ , false @*/); err != nil {
		panic(err) // Must work
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
	}, nil
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

// @ requires  acc(&p.d, R50) && acc(p.d.Mem(), _)
// @ requires  acc(p.scionLayer.Mem(ub), R4)
// @ requires  p.scionLayer.ValidPathMetaData(ub)
// @ requires  sl.Bytes(ub, 0, len(ub))
// @ requires  acc(&p.ingressID,  R50)
// @ requires  acc(&p.buffer, R55) && p.buffer != nil && p.buffer.Mem()
// @ requires  sl.Bytes(p.buffer.UBuf(), 0, len(p.buffer.UBuf()))
// @ requires  cause != nil ==> cause.ErrorMem()
// @ ensures   acc(&p.d, R50) && acc(p.d.Mem(), _)
// @ ensures   acc(p.scionLayer.Mem(ub), R4)
// @ ensures   sl.Bytes(ub, 0, len(ub))
// @ ensures   acc(&p.ingressID,  R50)
// @ ensures   acc(&p.buffer, R55) && p.buffer != nil && p.buffer.Mem()
// @ ensures   sl.Bytes(p.buffer.UBuf(), 0, len(p.buffer.UBuf()))
// @ ensures   result != nil ==>
// @ 	result === p.buffer.UBuf()
// @ ensures   reserr != nil && reserr.ErrorMem()
// @ ensures   result != nil ==>
// @ 	!slayers.IsSupportedPkt(result)
// @ decreases
func (p *slowPathPacketProcessor) prepareSCMP(
	typ slayers.SCMPType,
	code slayers.SCMPCode,
	scmpP gopacket.SerializableLayer,
	isError bool,
	// @ ghost ub []byte,
) (result []byte, reserr error) {

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
			return nil, serrors.JoinNoStack(cannotRoute, nil, "details", "unsupported path type",
				"path type", pathType)

		}
	case epic.PathType:
		epicPath, ok := p.scionLayer.Path.(*epic.Path)
		if !ok {
			// @ fold acc(p.scionLayer.Mem(ub), R4)
			return nil, serrors.JoinNoStack(cannotRoute, nil, "details", "unsupported path type",
				"path type", pathType)

		}
		// @ scionBuf := epicPath.GetUnderlyingScionPathBuf(ubPath)
		// @ unfold acc(epicPath.Mem(ubPath), R4)
		// @ assert ubPath[epic.MetadataLen:] === scionBuf
		// @ epicPathUb = ubPath
		// @ ubPath = scionBuf
		// @ startP += epic.MetadataLen
		// @ assert ubPath === ub[startP:endP]
		path = epicPath.ScionPath
		// @ pathFromEpic = true
	default:
		// @ fold acc(p.scionLayer.Mem(ub), R4)
		return nil, serrors.JoinNoStack(cannotRoute, nil, "details", "unsupported path type",
			"path type", pathType)

	}
	// @ assert pathType == scion.PathType || pathType == epic.PathType
	// @ assert typeOf(p.scionLayer.Path) == type[*scion.Raw] || typeOf(p.scionLayer.Path) == type[*epic.Path]
	// @ assert !pathFromEpic ==> typeOf(p.scionLayer.Path) == type[*scion.Raw]
	// @ assert pathFromEpic ==> typeOf(p.scionLayer.Path) == type[*epic.Path]
	// @ sl.SplitRange_Bytes(ub, startP, endP, writePerm)
	decPath, err := path.ToDecoded( /*@ ubPath @*/ )
	if err != nil {
		// @ sl.CombineRange_Bytes(ub, startP, endP, writePerm)
		// @ ghost if pathFromEpic {
		// @ 	epicPath := p.scionLayer.Path.(*epic.Path)
		// @ 	assert acc(path.Mem(ubPath), R4)
		// @ 	fold acc(epicPath.Mem(epicPathUb), R4)
		// @ } else {
		// @ 	rawPath := p.scionLayer.Path.(*scion.Raw)
		// @ 	assert acc(path.Mem(ubPath), R4)
		// @ 	assert acc(rawPath.Mem(ubPath), R4)
		// @ }
		// @ fold acc(p.scionLayer.Mem(ub), R4)
		return nil, serrors.JoinNoStack(cannotRoute, err, "details", "decoding raw path")
	}
	// @ ghost rawPath := path.RawBufferMem(ubPath)
	revPathTmp, err := decPath.Reverse( /*@ rawPath @*/ )
	if err != nil {
		// @ sl.CombineRange_Bytes(ub, startP, endP, writePerm)
		// @ ghost if pathFromEpic {
		// @ 	epicPath := p.scionLayer.Path.(*epic.Path)
		// @ 	assert acc(path.Mem(ubPath), R4)
		// @ 	fold acc(epicPath.Mem(epicPathUb), R4)
		// @ } else {
		// @ 	rawPath := p.scionLayer.Path.(*scion.Raw)
		// @ 	assert acc(path.Mem(ubPath), R4)
		// @ 	assert acc(rawPath.Mem(ubPath), R4)
		// @ }
		// @ fold acc(p.scionLayer.Mem(ub), R4)
		return nil, serrors.JoinNoStack(cannotRoute, err, "details", "reversing path for SCMP")
	}
	// @ assert revPathTmp.Mem(rawPath)
	revPath := revPathTmp.(*scion.Decoded)
	// @ assert revPath.Mem(rawPath)

	peering, err := determinePeer(revPath.PathMeta, revPath.InfoFields[revPath.PathMeta.CurrINF])
	if err != nil {
		return nil, serrors.JoinNoStack(cannotRoute, err, "details", "peering cannot be determined")
	}

	// Revert potential path segment switches that were done during processing.
	if revPath.IsXover( /*@ rawPath @*/ ) && !peering {
		// An effective cross-over is a change of segment other than at
		// a peering hop.
		if err := revPath.IncPath( /*@ rawPath @*/ ); err != nil {
			// @ sl.CombineRange_Bytes(ub, startP, endP, writePerm)
			// @ ghost if pathFromEpic {
			// @ 	epicPath := p.scionLayer.Path.(*epic.Path)
			// @ 	assert acc(path.Mem(ubPath), R4)
			// @ 	fold acc(epicPath.Mem(epicPathUb), R4)
			// @ } else {
			// @ 	rawPath := p.scionLayer.Path.(*scion.Raw)
			// @ 	assert acc(path.Mem(ubPath), R4)
			// @ 	assert acc(rawPath.Mem(ubPath), R4)
			// @ }
			// @ fold acc(p.scionLayer.Mem(ub), R4)
			return nil, serrors.JoinNoStack(cannotRoute, err,
				"details", "reverting cross over for SCMP")
		}
	}
	// If the packet is sent to an external router, we need to increment the
	// path to prepare it for the next hop.
	// @ p.d.getExternalMem()
	// @ if p.d.external != nil { unfold acc(accBatchConn(p.d.external), _) }
	_, external := p.d.external[p.pkt.ingress]
	if external {
		// @ requires revPath.Mem(rawPath)
		// @ requires revPath.GetBase(rawPath).Valid()
		// @ ensures  revPath.Mem(rawPath)
		// @ decreases
		// @ outline(
		// @ unfold revPath.Mem(rawPath)
		// @ unfold revPath.Base.Mem()
		infoField := &revPath.InfoFields[revPath.PathMeta.CurrINF]
		if infoField.ConsDir && !peering {
			hopField :=  /*@ unfolding acc(revPath.HopFields[revPath.PathMeta.CurrHF].Mem(), _) in @*/
				revPath.HopFields[revPath.PathMeta.CurrHF]
			infoField.UpdateSegID(hopField.Mac /*@, hopField.ToIO_HF() @*/)
		}
		// @ fold revPath.Base.Mem()
		// @ fold revPath.Mem(rawPath)
		// @ )
		if err := revPath.IncPath( /*@ rawPath @*/ ); err != nil {
			// @ sl.CombineRange_Bytes(ub, startP, endP, writePerm)
			// @ ghost if pathFromEpic {
			// @ 	epicPath := p.scionLayer.Path.(*epic.Path)
			// @ 	assert acc(path.Mem(ubPath), R4)
			// @ 	fold acc(epicPath.Mem(epicPathUb), R4)
			// @ } else {
			// @ 	rawPath := p.scionLayer.Path.(*scion.Raw)
			// @ 	assert acc(path.Mem(ubPath), R4)
			// @ 	assert acc(rawPath.Mem(ubPath), R4)
			// @ }
			// @ fold acc(p.scionLayer.Mem(ub), R4)
			return nil, serrors.JoinNoStack(cannotRoute, err,
				"details", "incrementing path for SCMP")
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
	scionL.DstAddrType = p.scionLayer.SrcAddrType
	scionL.RawDstAddr = p.scionLayer.RawSrcAddr
	scionL.NextHdr = slayers.L4SCMP

	if err := scionL.SetSrcAddr(addr.HostIP(p.d.internalIP)); err != nil {
		return nil, serrors.JoinNoStack(cannotRoute, err, "details", "setting src addr")
	}
	typeCode := slayers.CreateSCMPTypeCode(typ, code)
	scmpH /*@@@*/ := slayers.SCMP{TypeCode: typeCode}
	scmpH.SetNetworkLayerForChecksum(&scionL)

	needsAuth := false
	if p.d.ExperimentalSCMPAuthentication {
		// Error messages must be authenticated.
		// Traceroute are OPTIONALLY authenticated ONLY IF the request
		// was authenticated.
		// TODO(JordiSubira): Reuse the key computed in p.hasValidAuth
		// if SCMPTypeTracerouteReply to create the response.
		needsAuth = isError ||
			(scmpH.TypeCode.Type() == slayers.SCMPTypeTracerouteReply &&
				p.hasValidAuth(time.Now()))
	}

	var quote []byte
	if isError {
		// add quote for errors.
		hdrLen := slayers.CmnHdrLen + scionL.AddrHdrLen() + scionL.Path.Len()
		if needsAuth {
			hdrLen += e2eAuthHdrLen
		}
		switch scmpH.TypeCode.Type() {
		case slayers.SCMPTypeExternalInterfaceDown:
			hdrLen += 20
		case slayers.SCMPTypeInternalConnectivityDown:
			hdrLen += 28
		default:
			hdrLen += 8
		}
		quote = p.pkt.rawPacket
		maxQuoteLen := slayers.MaxSCMPPacketLen - hdrLen
		if len(quote) > maxQuoteLen {
			quote = quote[:maxQuoteLen]
		}
	}

	if err := p.buffer.Clear(); err != nil {
		return nil, err
	}
	sopts := gopacket.SerializeOptions{
		ComputeChecksums: true,
		FixLengths:       true,
	}
	// First write the SCMP message only without the SCION header(s) to get a buffer that we
	// can (re-)use as input in the MAC computation.
	// XXX(matzf) could we use iovec gather to avoid copying quote?
	err = gopacket.SerializeLayers(p.buffer, sopts, &scmpH, scmpP, gopacket.Payload(quote))
	if err != nil {
		return nil, serrors.JoinNoStack(cannotRoute, err, "details", "serializing SCMP message")
	}

	if needsAuth {
		var e2e slayers.EndToEndExtn
		scionL.NextHdr = slayers.End2EndClass

		now := time.Now()
		dstA, err := scionL.DstAddr()
		if err != nil {
			return nil, serrors.JoinNoStack(cannotRoute, err,
				"details", "parsing destination address")
		}
		key, err := p.drkeyProvider.GetASHostKey(now, scionL.DstIA, dstA)
		if err != nil {
			return nil, serrors.JoinNoStack(cannotRoute, err, "details", "retrieving DRKey")
		}
		if err := p.resetSPAOMetadata(key, now); err != nil {
			return nil, serrors.JoinNoStack(cannotRoute, err, "details", "resetting SPAO header")
		}

		e2e.Options = []*slayers.EndToEndOption{p.optAuth.EndToEndOption}
		e2e.NextHdr = slayers.L4SCMP
		_, err = spao.ComputeAuthCMAC(
			spao.MACInput{
				Key:        key.Key[:],
				Header:     p.optAuth,
				ScionLayer: &scionL,
				PldType:    slayers.L4SCMP,
				Pld:        p.buffer.Bytes(),
			},
			p.macInputBuffer,
			p.optAuth.Authenticator(),
		)
		if err != nil {
			return nil, serrors.JoinNoStack(cannotRoute, err, "details", "computing CMAC")
		}
		if err := e2e.SerializeTo(p.buffer, sopts); err != nil {
			return nil, serrors.JoinNoStack(cannotRoute, err,
				"details", "serializing SCION E2E headers")
		}
	} else {
		scionL.NextHdr = slayers.L4SCMP
	}
	if err := scionL.SerializeTo(p.buffer, sopts); err != nil {
		return nil, serrors.JoinNoStack(cannotRoute, err, "details", "serializing SCION header")
	}

	log.Debug("scmp", "typecode", scmpH.TypeCode)
	return p.buffer.Bytes(), nil
}

func (p *slowPathPacketProcessor) resetSPAOMetadata(key drkey.ASHostKey, now time.Time) error {
	// For creating SCMP responses we use sender side.
	dir := slayers.PacketAuthSenderSide
	drkeyType := slayers.PacketAuthASHost

	spi, err := slayers.MakePacketAuthSPIDRKey(uint16(drkey.SCMP), drkeyType, dir)
	if err != nil {
		return err
	}

	timestamp, err := spao.RelativeTimestamp(key.Epoch, now)
	if err != nil {
		return err
	}

	return p.optAuth.Reset(slayers.PacketAuthOptionParams{
		SPI:         spi,
		Algorithm:   slayers.PacketAuthCMAC,
		TimestampSN: timestamp,
		Auth:        zeroBuffer,
	})
}

func (p *slowPathPacketProcessor) hasValidAuth(t time.Time) bool {
	// Check if e2eLayer was parsed for this packet
	if !p.lastLayer.CanDecode().Contains(slayers.LayerTypeEndToEndExtn) {
		return false
	}
	// Parse incoming authField
	e2eLayer := &slayers.EndToEndExtn{}
	if err := e2eLayer.DecodeFromBytes(
		p.e2eLayer.Contents,
		gopacket.NilDecodeFeedback,
	); err != nil {
		return false
	}
	e2eOption, err := e2eLayer.FindOption(slayers.OptTypeAuthenticator)
	if err != nil {
		return false
	}
	authOption, err := slayers.ParsePacketAuthOption(e2eOption)
	if err != nil {
		return false
	}
	// Computing authField
	// the sender should have used the receiver side key, i.e., K_{localIA-remoteIA:remoteHost}
	// where remoteIA == p.scionLayer.SrcIA and remoteHost == srcAddr
	// (for the incoming packet).
	srcAddr, err := p.scionLayer.SrcAddr()
	if err != nil {
		return false
	}
	key, err := p.drkeyProvider.GetKeyWithinAcceptanceWindow(
		t,
		authOption.TimestampSN(),
		p.scionLayer.SrcIA,
		srcAddr,
	)
	if err != nil {
		log.Debug("Selecting key to authenticate the incoming packet", "err", err)
		return false
	}

	_, err = spao.ComputeAuthCMAC(
		spao.MACInput{
			Key:        key.Key[:],
			Header:     authOption,
			ScionLayer: &p.scionLayer,
			PldType:    slayers.L4SCMP,
			Pld:        p.lastLayer.LayerPayload(),
		},
		p.macInputBuffer,
		p.validAuthBuf,
	)
	if err != nil {
		return false
	}
	// compare incoming authField with computed authentication tag
	return subtle.ConstantTimeCompare(authOption.Authenticator(), p.validAuthBuf) != 0
}

// decodeLayers implements roughly the functionality of
// gopacket.DecodingLayerParser, but customized to our use case with a "base"
// layer and additional, optional layers in the given order.
// Returns the last decoded layer.
// @ requires  base != nil && base.NonInitMem()
// @ requires  forall i int :: { &opts[i] } 0 <= i && i < len(opts) ==>
// @ 	(acc(&opts[i], R10) && opts[i] != nil && opts[i].NonInitMem())
// Due to Viper's very strict injectivity constraints:
// @ requires  forall i, j int :: { &opts[i], &opts[j] } 0 <= i && i < j && j < len(opts) ==>
// @ 	opts[i] !== opts[j]
// @ preserves acc(sl.Bytes(data, 0, len(data)), R39)
// @ ensures   forall i int :: { &opts[i] } 0 <= i && i < len(opts) ==>
// @ 	(acc(&opts[i], R10) && opts[i] != nil)
// @ ensures   -1 <= idx && idx < len(opts)
// @ ensures   len(processed) == len(opts)
// @ ensures   len(offsets) == len(opts)
// @ ensures   reterr == nil && 0 <= idx ==> processed[idx]
// @ ensures   reterr == nil && idx == -1  ==> retl === base
// @ ensures   reterr == nil && 0 <= idx ==> retl === opts[idx]
// @ ensures   reterr == nil ==> retl != nil
// @ ensures   reterr == nil ==> base.Mem(data)
// @ ensures   reterr == nil && typeOf(base.GetPath(data)) == *scion.Raw ==>
// @ 	base.EqAbsHeader(data) && base.ValidScionInitSpec(data)
// @ ensures   reterr == nil ==> base.EqPathType(data)
// @ ensures   forall i int :: {&opts[i]}{processed[i]} 0 <= i && i < len(opts) ==>
// @ 	(processed[i] ==> (0 <= offsets[i].start && offsets[i].start <= offsets[i].end && offsets[i].end <= len(data)))
// @ ensures   reterr == nil ==> forall i int :: {&opts[i]}{processed[i]} 0 <= i && i < len(opts) ==>
// @ 	((processed[i] && !offsets[i].isNil) ==> opts[i].Mem(data[offsets[i].start:offsets[i].end]))
// @ ensures   reterr == nil ==> forall i int :: {&opts[i]}{processed[i]} 0 <= i && i < len(opts) ==>
// @ 	((processed[i] && offsets[i].isNil) ==> opts[i].Mem(nil))
// @ ensures   reterr == nil ==> forall i int :: {&opts[i]}{processed[i]} 0 <= i && i < len(opts) ==>
// @ 	(!processed[i] ==> opts[i].NonInitMem())
// @ ensures   reterr != nil ==> base.NonInitMem()
// @ ensures   reterr != nil ==> (forall i int :: { &opts[i] } 0 <= i && i < len(opts) ==> opts[i].NonInitMem())
// @ ensures   reterr != nil ==> reterr.ErrorMem()
// @ decreases
// (VerifiedSCION) originally, `base` was declared with type `gopacket.DecodingLayer`. This is unnecessarily complicated for a private function
// that is only called once with a parameter of type `*SCION`, and leads to more annyoing post-conditions.
func decodeLayers(data []byte, base *slayers.SCION, opts ...gopacket.DecodingLayer) (
	retl gopacket.DecodingLayer,
	reterr error,
	// @ ghost processed seq[bool],
	// @ ghost offsets seq[offsetPair],
	// @ ghost idx int,
) {
	// @ processed = seqs.NewSeqBool(len(opts))
	// @ offsets = newOffsetPair(len(opts))
	// @ idx = -1
	// @ gopacket.AssertInvariantNilDecodeFeedback()
	if err := base.DecodeFromBytes(data, gopacket.NilDecodeFeedback); err != nil {
		return nil, err /*@ , processed, offsets, idx @*/
	}
	var last gopacket.DecodingLayer = base
	optsSlice := ([](gopacket.DecodingLayer))(opts)

	// @ ghost oldData := data
	// @ ghost oldStart := 0
	// @ ghost oldEnd := len(data)

	// @ invariant acc(sl.Bytes(oldData, 0, len(oldData)), R39)
	// @ invariant base.Mem(oldData)
	// @ invariant typeOf(base.GetPath(oldData)) == *scion.Raw ==>
	// @ 	base.EqAbsHeader(oldData) && base.ValidScionInitSpec(oldData)
	// @ invariant base.EqPathType(oldData)
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
	// @ 	(processed[i] ==> (0 <= offsets[i].start && offsets[i].start <= offsets[i].end && offsets[i].end <= len(data)))
	// @ invariant forall i int :: {&opts[i]}{processed[i]} 0 <= i && i < len(opts) ==>
	// @ 	((processed[i] && !offsets[i].isNil) ==> opts[i].Mem(oldData[offsets[i].start:offsets[i].end]))
	// @ invariant forall i int :: {&opts[i]}{processed[i]} 0 <= i && i < len(opts) ==>
	// @ 	((processed[i] && offsets[i].isNil) ==> opts[i].Mem(nil))
	// @ invariant forall i int :: {&opts[i]}{processed[i]} 0 < len(opts) && i0 <= i && i < len(opts) ==>
	// @ 	!processed[i]
	// @ invariant forall i int :: {&opts[i]}{processed[i]} 0 <= i && i < len(opts) ==>
	// @ 	(!processed[i] ==> opts[i].NonInitMem())
	// @ invariant gopacket.NilDecodeFeedback.Mem()
	// @ invariant 0 <= oldStart && oldStart <= oldEnd && oldEnd <= len(oldData)
	// @ decreases len(opts) - i0
	for _, opt := range optsSlice /*@ with i0 @*/ {
		layerClassTmp := opt.CanDecode()
		// @ fold layerClassTmp.Mem()
		// @ ghost var pos offsetPair
		// @ ghost var ub []byte
		// @ ghost if idx == -1 {
		// @ 	pos = offsetPair{0, len(oldData), false}
		// @ 	ub = oldData
		// @ } else {
		// @ 	pos = offsets[idx]
		// @ 	if pos.isNil { ub = nil } else { ub  = oldData[pos.start:pos.end] }
		// @ }
		if layerClassTmp.Contains(last.NextLayerType( /*@ ub @*/ )) {
			data /*@ , start, end @*/ := last.LayerPayload( /*@ ub @*/ )
			// @ assert data == nil || data === oldData[pos.start:pos.end][start:end]
			// @ oldEnd   = pos.start + end
			// @ oldStart = pos.start + start
			// @ ghost if data == nil {
			// @ 	sl.NilAcc_Bytes()
			// @ } else {
			// @ 	sl.SplitRange_Bytes(oldData, oldStart, oldEnd, R40)
			// @ }
			if err := opt.DecodeFromBytes(data, gopacket.NilDecodeFeedback); err != nil {
				// @ ghost if data != nil { sl.CombineRange_Bytes(oldData, oldStart, oldEnd, R40) }
				// @ base.DowngradePerm(oldData)

				// ghost clean-up:
				// @ ghost
				// @ invariant -1 <= c && c < i0
				// @ invariant len(processed) == len(opts)
				// @ invariant len(offsets) == len(opts)
				// @ invariant forall i int :: {&opts[i]} 0 <= i && i < len(opts) ==> acc(&opts[i], R10)
				// @ invariant forall i, j int :: {&opts[i], &opts[j]} 0 <= i && i < j && j < len(opts) ==> opts[i] !== opts[j]
				// @ invariant forall i int :: {&opts[i]} 0 <= i && i < len(opts) ==> opts[i] != nil
				// @ invariant forall i int :: {&opts[i]}{processed[i]} 0 <= i && i < len(opts) ==>
				// @ 	(processed[i] ==> (0 <= offsets[i].start && offsets[i].start <= offsets[i].end && offsets[i].end <= len(oldData)))
				// @ invariant forall i int :: {&opts[i]}{processed[i]} 0 <= i && i < len(opts) ==>
				// @ 	((processed[i] && !offsets[i].isNil) ==> opts[i].Mem(oldData[offsets[i].start:offsets[i].end]))
				// @ invariant forall i int :: {&opts[i]}{processed[i]} 0 <= i && i < len(opts) ==>
				// @ 	((processed[i] && offsets[i].isNil) ==> opts[i].Mem(nil))
				// @ invariant forall i int :: {&opts[i]}{processed[i]} 0 <= i && i < len(opts) ==>
				// @ 	(!processed[i] ==> opts[i].NonInitMem())
				// @ invariant forall i int :: {&opts[i]}{processed[i]} 0 < len(opts) && c < i && i < len(opts) ==>
				// @ 	!processed[i]
				// @ decreases c
				// @ for c := i0-1; 0 <= c; c=c-1 {
				// @ 	if processed[c] {
				// @ 		off := offsets[c]
				// @ 		if off.isNil {
				// @ 			opts[c].DowngradePerm(nil)
				// @ 		} else {
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
			// @ ghost if data != nil { sl.CombineRange_Bytes(oldData, oldStart, oldEnd, R40) }
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

// initMetrics initializes the metrics related to packet forwarding. The counters are already
// instantiated for all the relevant interfaces so this will not have to be repeated during packet
// forwarding.
func (d *DataPlane) initMetrics() {
	d.forwardingMetrics = make(map[uint16]interfaceMetrics)
	d.forwardingMetrics[0] = newInterfaceMetrics(d.Metrics, 0, d.localIA, d.neighborIAs)
	for ifID := range d.external {
		if _, notOwned := d.internalNextHops[ifID]; notOwned {
			continue
		}
		d.forwardingMetrics[ifID] = newInterfaceMetrics(d.Metrics, ifID, d.localIA, d.neighborIAs)
	}

	// Start our custom /proc/pid/stat collector to export iowait time and (in the future) other
	// process-wide metrics that prometheus does not.
	err := processmetrics.Init()

	// we can live without these metrics. Just log the error.
	if err != nil {
		log.Error("Could not initialize processmetrics", "err", err)
	}
}

// updateNetAddrFromAddrPort() updates a net.UDPAddr address to be the same as the
// given netip.AddrPort. newDst.Addr() returns the IP by value. The compiler may or
// may not inline the call and optimize out the copy. It is doubtful that manually inlining
// increases the chances that the copy get elided. TODO(jiceatscion): experiment.
func updateNetAddrFromAddrPort(netAddr *net.UDPAddr, newDst netip.AddrPort) {
	updateNetAddrFromAddrAndPort(netAddr, newDst.Addr(), newDst.Port())
}

// updateNetAddrFromAddrAndPort() updates a net.UDPAddr address to be the same IP and port as
// the given netip.Addr and unigned port.
//
// We handle dstAddr so we don't make the GC work. The issue is the IP address slice
// that's in dstAddr. The packet, along with its address and IP slice, gets copied from a channel
// into a local variable. Then after we modify it, all gets copied to the some other channel and
// eventually it gets copied back to the pool. If we replace the destAddr.IP at any point,
// the old backing array behind the destAddr.IP slice ends-up on the garbage pile. To prevent that,
// we update the IP address in-place (we make the length 0 to represent the 0 address).
func updateNetAddrFromAddrAndPort(netAddr *net.UDPAddr, addr netip.Addr, port uint16) {
	netAddr.Port = int(port)
	netAddr.Zone = addr.Zone()
	if addr.Is4() {
		outIpBytes := addr.As4()     // Must store explicitly in order to copy
		netAddr.IP = netAddr.IP[0:4] // Update slice
		copy(netAddr.IP, outIpBytes[:])
	} else if addr.Is6() {
		outIpBytes := addr.As16()
		netAddr.IP = netAddr.IP[0:16]
		copy(netAddr.IP, outIpBytes[:])
	} else {
		// That's a zero address. We translate in to something resembling a nil IP.
		// Nothing gets discarded as we keep the slice (and its reference to the backing array).
		// To that end, we cannot make it nil. We have to make its length zero.
		netAddr.IP = netAddr.IP[0:0]
	}
}

// updateNetAddrFromNetAddr() copies fromNetAddr into netAddr while re-using the IP slice
// embedded in netAddr. This is to avoid giving work to the GC. Nil IPs get
// converted into empty slices. The backing array isn't discarded.
func updateNetAddrFromNetAddr(netAddr *net.UDPAddr, fromNetAddr *net.UDPAddr) {
	netAddr.Port = fromNetAddr.Port
	netAddr.Zone = fromNetAddr.Zone
	netAddr.IP = netAddr.IP[0:len(fromNetAddr.IP)]
	copy(netAddr.IP, fromNetAddr.IP)
}
