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

// @ initEnsures acc(path.PathPackageMem(), _)
// @ initEnsures path.Registered(empty.PathType)
// @ initEnsures path.Registered(scion.PathType)
// @ initEnsures path.Registered(onehop.PathType)
// @ initEnsures path.Registered(epic.PathType)
package slayers

import (
	"encoding/binary"
	"net"

	"github.com/google/gopacket"

	"github.com/scionproto/scion/pkg/addr"
	"github.com/scionproto/scion/pkg/private/serrors"

	// @ importRequires path.PathPackageMem()
	// @ importRequires !path.Registered(0) && !path.Registered(1)
	// @ importRequires !path.Registered(2) && !path.Registered(3)
	"github.com/scionproto/scion/pkg/slayers/path"
	"github.com/scionproto/scion/pkg/slayers/path/empty"
	"github.com/scionproto/scion/pkg/slayers/path/epic"
	"github.com/scionproto/scion/pkg/slayers/path/onehop"
	"github.com/scionproto/scion/pkg/slayers/path/scion"
	// @ b "github.com/scionproto/scion/verification/utils/bitwise"
	// @ def "github.com/scionproto/scion/verification/utils/definitions"
	// @ sl "github.com/scionproto/scion/verification/utils/slices"
)

const (
	// LineLen is the length of a SCION header line in bytes.
	LineLen = 4
	// CmnHdrLen is the length of the SCION common header in bytes.
	CmnHdrLen = 12
	// MaxHdrLen is the maximum allowed length of a SCION header in bytes.
	MaxHdrLen = 1020
	// SCIONVersion is the currently supported version of the SCION header format. Different
	// versions are not guaranteed to be compatible to each other.
	SCIONVersion = 0
)

func init() {
	empty.RegisterPath()
	scion.RegisterPath()
	onehop.RegisterPath()
	epic.RegisterPath()
}

// AddrType indicates the type of a host address in the SCION header.
// The AddrType consists of a sub-type and length part, both two bits wide.
// The four possible lengths are 4B (0), 8B (1), 12B (2), or 16B (3) bytes.
// There are four possible sub-types per address length.
type AddrType uint8

// AddrType constants
const (
	T4Ip  AddrType = 0b0000 // T=0, L=0
	T4Svc          = 0b0100 // T=1, L=0
	T16Ip          = 0b0011 // T=0, L=3
)

// Length returns the length of this AddrType value.
// (VerifiedSCION) Assumed, as Gobra cannot reason about the result of bitwise operations.
// @ pure
// @ requires tl.Has3Bits()
// @ ensures  res == LineLen * (1 + (b.BitAnd3(int(tl))))
// @ ensures  tl == T4Ip  ==> res == LineLen
// @ ensures  tl == T4Svc ==> res == LineLen
// @ ensures  tl == T16Ip ==> res == 4*LineLen
// @ decreases
func (tl AddrType) Length() (res int) {
	return LineLen * (1 + (int(tl) & 0x3))
}

// BaseLayer is a convenience struct which implements the LayerData and
// LayerPayload functions of the Layer interface.
// Copy-pasted from gopacket/layers (we avoid importing this due its massive size)
type BaseLayer struct {
	// Contents is the set of bytes that make up this layer.  IE: for an
	// Ethernet packet, this would be the set of bytes making up the
	// Ethernet frame.
	Contents []byte
	// Payload is the set of bytes contained by (but not part of) this
	// Layer.  Again, to take Ethernet as an example, this would be the
	// set of bytes encapsulated by the Ethernet protocol.
	Payload []byte
}

// LayerContents returns the bytes of the packet layer.
// @ requires b.LayerMem()
// @ ensures  sl.AbsSlice_Bytes(res, 0, len(res))
// @ ensures  sl.AbsSlice_Bytes(res, 0, len(res)) --* b.LayerMem()
// @ decreases
func (b *BaseLayer) LayerContents() (res []byte) {
	//@ unfold b.LayerMem()
	//@ unfold sl.AbsSlice_Bytes(b.Contents, 0, len(b.Contents))
	res = b.Contents
	//@ fold sl.AbsSlice_Bytes(res, 0, len(res))
	//@ package sl.AbsSlice_Bytes(res, 0, len(res)) --* b.LayerMem() {
	//@   fold b.LayerMem()
	//@ }
	return res
}

// LayerPayload returns the bytes contained within the packet layer.
// @ requires b.PayloadMem()
// @ ensures sl.AbsSlice_Bytes(res, 0, len(res))
// @ ensures sl.AbsSlice_Bytes(res, 0, len(res)) --* b.PayloadMem()
// @ decreases
func (b *BaseLayer) LayerPayload() (res []byte) {
	//@ unfold b.PayloadMem()
	//@ unfold sl.AbsSlice_Bytes(b.Payload, 0, len(b.Payload))
	res = b.Payload
	//@ fold sl.AbsSlice_Bytes(res, 0, len(res))
	//@ package sl.AbsSlice_Bytes(res, 0, len(res)) --* b.PayloadMem() {
	//@   fold b.PayloadMem()
	//@ }
	return res
}

// SCION is the header of a SCION packet.
type SCION struct {
	BaseLayer
	// Common Header fields

	// Version is version of the SCION Header. Currently, only 0 is supported.
	Version uint8
	// TrafficClass denotes the traffic class. Its value in a received packet or fragment might be
	// different from the value sent by the packet’s source. The current use of the Traffic Class
	// field for Differentiated Services and Explicit Congestion Notification is specified in
	// RFC2474 and RFC3168
	TrafficClass uint8
	// FlowID is a 20-bit field used by a source to label sequences of packets to be treated in the
	// network as a single flow. It is mandatory to be set.
	FlowID uint32
	// NextHdr  encodes the type of the first header after the SCION header. This can be either a
	// SCION extension or a layer-4 protocol such as TCP or UDP. Values of this field respect and
	// extend IANA’s assigned internet protocol numbers.
	NextHdr L4ProtocolType
	// HdrLen is the length of the SCION header in multiples of 4 bytes. The SCION header length is
	// computed as HdrLen * 4 bytes. The 8 bits of the HdrLen field limit the SCION header to a
	// maximum of 255 * 4 == 1020 bytes.
	HdrLen uint8
	// PayloadLen is the length of the payload in bytes. The payload includes extension headers and
	// the L4 payload. This field is 16 bits long, supporting a maximum payload size of 64KB.
	PayloadLen uint16
	// PathType specifies the type of path in this SCION header.
	PathType path.Type
	// DstAddrType (4 bit) is the type/length of the destination address.
	DstAddrType AddrType
	// SrcAddrType (4 bit) is the type/length of the source address.
	SrcAddrType AddrType

	// Address header fields.

	// DstIA is the destination ISD-AS.
	DstIA addr.IA
	// SrcIA is the source ISD-AS.
	SrcIA addr.IA
	// RawDstAddr is the destination address.
	RawDstAddr []byte
	// RawSrcAddr is the source address.
	RawSrcAddr []byte

	// Path is the path contained in the SCION header. It depends on the PathType field.
	Path path.Path

	pathPool    []path.Path
	pathPoolRaw path.Path
}

// @ ensures res === LayerTypeSCION
// @ decreases
// @ pure
func (s *SCION) LayerType() (res gopacket.LayerType) {
	return LayerTypeSCION
}

// @ ensures res === LayerClassSCION
// @ decreases
func (s *SCION) CanDecode() (res gopacket.LayerClass) {
	return LayerClassSCION
}

// @ preserves acc(s.Mem(ub), def.ReadL20)
// @ decreases
func (s *SCION) NextLayerType( /*@ ghost ub []byte @*/ ) gopacket.LayerType {
	return scionNextLayerType( /*@ unfolding acc(s.Mem(ub), def.ReadL20) in @*/ s.NextHdr)
}

// @ trusted
// @ requires false
func (s *SCION) LayerPayload() []byte {
	return s.Payload
}

// @ ensures res == gopacket.Flow{}
// @ decreases
func (s *SCION) NetworkFlow() (res gopacket.Flow) {
	// TODO(shitz): Investigate how we can use gopacket.Flow.
	return gopacket.Flow{}
}

// @ requires  !opts.FixLengths
// @ requires  b != nil && b.Mem(uSerBuf)
// @ preserves acc(s.Mem(ubuf), def.ReadL10)
// @ ensures   b.Mem(uSerBuf) // TODO: use the new value
// @ decreases
func (s *SCION) SerializeTo(b gopacket.SerializeBuffer, opts gopacket.SerializeOptions /* @ , ghost ubuf []byte, ghost uSerBuf []byte @*/) error {
	// @ unfold acc(s.Mem(ubuf), def.ReadL10)
	// @ defer  fold acc(s.Mem(ubuf), def.ReadL10)
	scnLen := CmnHdrLen + s.AddrHdrLen( /*@ nil, true @*/ ) + s.Path.Len( /*@ ubuf[CmnHdrLen+s.AddrHdrLen(nil, true) : s.HdrLen*LineLen] @*/ )
	if scnLen > MaxHdrLen {
		return serrors.New("header length exceeds maximum",
			"max", MaxHdrLen, "actual", scnLen)
	}
	if scnLen%LineLen != 0 {
		return serrors.New("header length is not an integer multiple of line length",
			"actual", scnLen)
	}
	buf, err /*@ , uSerBufN @*/ := b.PrependBytes(scnLen /*@, uSerBuf @*/)
	if err != nil {
		return err
	}
	if opts.FixLengths {
		// @ def.Unreachable()
		s.HdrLen = uint8(scnLen / LineLen)
		s.PayloadLen = uint16(len(b.Bytes( /*@ uSerBufN @*/ )) - scnLen)
	}
	// @ assert buf === uSerBufN[:scnLen]
	// @ b.ExchangePred(uSerBufN)
	// @ sl.SplitRange_Bytes(uSerBufN, 0, scnLen, writePerm)

	// Serialize common header.
	firstLine := uint32(s.Version&0xF)<<28 | uint32(s.TrafficClass)<<20 | s.FlowID&0xFFFFF
	// @ sl.SplitRange_Bytes(buf, 0, 4, writePerm)
	// @ unfold acc(sl.AbsSlice_Bytes(buf[:4], 0, 4), writePerm)
	binary.BigEndian.PutUint32(buf[:4], firstLine)
	// @ fold acc(sl.AbsSlice_Bytes(buf[:4], 0, 4), writePerm)
	// @ sl.CombineRange_Bytes(buf, 0, 4, writePerm)
	// @ unfold acc(sl.AbsSlice_Bytes(buf, 0, len(buf)), writePerm)
	buf[4] = uint8(s.NextHdr)
	buf[5] = s.HdrLen
	// @ fold acc(sl.AbsSlice_Bytes(buf, 0, len(buf)), writePerm)
	// @ sl.SplitRange_Bytes(buf, 6, 8, writePerm)
	// @ unfold acc(sl.AbsSlice_Bytes(buf[6:8], 0, 2), writePerm)
	binary.BigEndian.PutUint16(buf[6:8], s.PayloadLen)
	// @ fold acc(sl.AbsSlice_Bytes(buf[6:8], 0, 2), writePerm)
	// @ sl.CombineRange_Bytes(buf, 6, 8, writePerm)
	// @ unfold acc(sl.AbsSlice_Bytes(buf, 0, len(buf)), writePerm)
	buf[8] = uint8(s.PathType)
	buf[9] = uint8(s.DstAddrType&0x7)<<4 | uint8(s.SrcAddrType&0x7)
	// @ fold acc(sl.AbsSlice_Bytes(buf, 0, len(buf)), writePerm)
	// @ sl.SplitRange_Bytes(buf, 10, 12, writePerm)
	// @ unfold acc(sl.AbsSlice_Bytes(buf[10:12], 0, 2), writePerm)
	binary.BigEndian.PutUint16(buf[10:12], 0)
	// @ fold acc(sl.AbsSlice_Bytes(buf[10:12], 0, 2), writePerm)
	// @ sl.CombineRange_Bytes(buf, 10, 12, writePerm)

	// Serialize address header.
	// @ sl.SplitRange_Bytes(buf, CmnHdrLen, len(buf), writePerm)
	// @ sl.SplitRange_Bytes(ubuf, CmnHdrLen, len(ubuf), writePerm)
	if err := s.SerializeAddrHdr(buf[CmnHdrLen:] /*@ , ubuf[CmnHdrLen:] @*/); err != nil {
		// @ sl.CombineRange_Bytes(buf, CmnHdrLen, len(buf), writePerm)
		return err
	}
	// @ assert false
	// @ sl.CombineRange_Bytes(buf, CmnHdrLen, len(buf), def.ReadL10)
	offset := CmnHdrLen + s.AddrHdrLen( /*@ nil, true @*/ )
	// @ assert false

	// Serialize path header.
	return s.Path.SerializeTo(buf[offset:] /*@, nil @*/)
	// TODO: combine range
	// TODO: apply wand from ExchangePred
}

// DecodeFromBytes decodes the SCION layer. DecodeFromBytes resets the internal state of this layer
// to the state defined by the passed-in bytes. Slices in the SCION layer reference the passed-in
// data, so care should be taken to copy it first should later modification of data be required
// before the SCION layer is discarded.
// @ requires  s.NonInitMem() && s.InitPathPool()
// @ requires  sl.AbsSlice_Bytes(data, 0, len(data))
// @ preserves df != nil && df.Mem()
// @ ensures   res == nil ==> s.Mem(data)
// @ ensures   res != nil ==> (s.NonInitMem() && sl.AbsSlice_Bytes(data, 0, len(data)) &&
// @	res.ErrorMem())
// @ decreases
func (s *SCION) DecodeFromBytes(data []byte, df gopacket.DecodeFeedback) (res error) {
	// Decode common header.
	if len(data) < CmnHdrLen {
		df.SetTruncated()
		return serrors.New("packet is shorter than the common header length",
			"min", CmnHdrLen, "actual", len(data))
	}
	// @ sl.SplitRange_Bytes(data, 0, 4, def.ReadL15)
	// @ preserves 4 <= len(data) && acc(sl.AbsSlice_Bytes(data[:4], 0, 4), def.ReadL15)
	// @ decreases
	// @ outline(
	// @ unfold acc(sl.AbsSlice_Bytes(data[:4], 0, 4), def.ReadL15)
	firstLine := binary.BigEndian.Uint32(data[:4])
	// @ fold acc(sl.AbsSlice_Bytes(data[:4], 0, 4), def.ReadL15)
	// @ )
	// @ sl.CombineRange_Bytes(data, 0, 4, def.ReadL15)
	// @ unfold s.NonInitMem()
	s.Version = uint8(firstLine >> 28)
	s.TrafficClass = uint8((firstLine >> 20) & 0xFF)
	s.FlowID = firstLine & 0xFFFFF
	// @ preserves acc(&s.NextHdr) && acc(&s.HdrLen) && acc(&s.PayloadLen) && acc(&s.PathType)
	// @ preserves acc(&s.DstAddrType) && acc(&s.SrcAddrType)
	// @ preserves CmnHdrLen <= len(data) && acc(sl.AbsSlice_Bytes(data, 0, len(data)), def.ReadL15)
	// @ ensures   s.DstAddrType.Has3Bits() && s.SrcAddrType.Has3Bits()
	// @ decreases
	// @ outline(
	// @ unfold acc(sl.AbsSlice_Bytes(data, 0, len(data)), def.ReadL15)
	s.NextHdr = L4ProtocolType(data[4])
	s.HdrLen = data[5]
	// @ assert &data[6:8][0] == &data[6] && &data[6:8][1] == &data[7]
	s.PayloadLen = binary.BigEndian.Uint16(data[6:8])
	s.PathType = path.Type(data[8])
	s.DstAddrType = AddrType(data[9] >> 4 & 0x7)
	// @ assert int(s.DstAddrType) == b.BitAnd7(int(data[9] >> 4))
	s.SrcAddrType = AddrType(data[9] & 0x7)
	// @ assert int(s.SrcAddrType) == b.BitAnd7(int(data[9]))
	// @ fold acc(sl.AbsSlice_Bytes(data, 0, len(data)), def.ReadL15)
	// @ )
	// Decode address header.
	// @ sl.SplitByIndex_Bytes(data, 0, len(data), CmnHdrLen, def.ReadL5)
	// @ sl.Reslice_Bytes(data, CmnHdrLen, len(data), def.ReadL5)
	if err := s.DecodeAddrHdr(data[CmnHdrLen:]); err != nil {
		// @ fold s.NonInitMem()
		// @ sl.Unslice_Bytes(data, CmnHdrLen, len(data), def.ReadL5)
		// @ sl.CombineAtIndex_Bytes(data, 0, len(data), CmnHdrLen, def.ReadL5)
		df.SetTruncated()
		return err
	}
	// @ sl.Unslice_Bytes(data, CmnHdrLen, len(data), def.ReadL5)
	// @ sl.CombineAtIndex_Bytes(data, 0, len(data), CmnHdrLen, def.ReadL5)
	// (VerifiedSCION) the first ghost parameter to AddrHdrLen is ignored when the second
	//                 is set to nil. As such, we pick the easiest possible value as a placeholder.
	addrHdrLen := s.AddrHdrLen( /*@ nil, true @*/ )
	offset := CmnHdrLen + addrHdrLen

	// Decode path header.
	var err error
	hdrBytes := int(s.HdrLen) * LineLen
	pathLen := hdrBytes - CmnHdrLen - addrHdrLen
	if pathLen < 0 {
		// @ unfold s.HeaderMem(data[CmnHdrLen:])
		// @ fold s.NonInitMem()
		return serrors.New("invalid header, negative pathLen",
			"hdrBytes", hdrBytes, "addrHdrLen", addrHdrLen, "CmdHdrLen", CmnHdrLen)
	}
	if minLen := offset + pathLen; len(data) < minLen {
		df.SetTruncated()
		// @ unfold s.HeaderMem(data[CmnHdrLen:])
		// @ fold s.NonInitMem()
		return serrors.New("provided buffer is too small", "expected", minLen, "actual", len(data))
	}

	s.Path, err = s.getPath(s.PathType)
	if err != nil {
		// @ def.Unreachable()
		return err
	}
	// (VerifiedSCION) Gobra cannot currently prove this, even though it must hold as s.PathType is of type
	//                 path.Type (defined as uint8)
	// @ assume 0 <= s.PathType
	// @ ghost if s.PathType == empty.PathType { fold s.Path.NonInitMem() }
	// @ sl.SplitRange_Bytes(data, offset, offset+pathLen, writePerm)
	err = s.Path.DecodeFromBytes(data[offset : offset+pathLen])
	if err != nil {
		// @ sl.CombineRange_Bytes(data, offset, offset+pathLen, writePerm)
		// @ unfold s.HeaderMem(data[CmnHdrLen:])
		// @ fold s.NonInitMem()
		return err
	}
	s.Contents = data[:hdrBytes]
	s.Payload = data[hdrBytes:]

	// @ fold s.Mem(data)

	return nil
}

// RecyclePaths enables recycling of paths used for DecodeFromBytes. This is
// only useful if the layer itself is reused.
// When this is enabled, the Path instance may be overwritten in
// DecodeFromBytes. No references to Path should be kept in use between
// invocations of DecodeFromBytes.
// @ requires s.NonInitPathPool()
// @ ensures  s.InitPathPool()
// @ decreases
func (s *SCION) RecyclePaths() {
	// @ unfold s.NonInitPathPool()
	if s.pathPool == nil {
		s.pathPool = []path.Path{
			empty.PathType:  empty.Path{},
			onehop.PathType: ( /*@ FoldOneHopMem( @*/ &onehop.Path{} /*@ ) @*/),
			scion.PathType:  ( /*@ FoldRawMem( @*/ &scion.Raw{} /*@ ) @*/),
			epic.PathType:   ( /*@ FoldEpicMem( @*/ &epic.Path{} /*@ ) @*/),
		}
		s.pathPoolRaw = path.NewRawPath()
		// @ assert acc(&s.pathPool[empty.PathType]) && acc(&s.pathPool[onehop.PathType])
		// @ assert acc(&s.pathPool[scion.PathType]) && acc(&s.pathPool[epic.PathType])
		// @ assert s.pathPool[onehop.PathType].NonInitMem() && s.pathPool[scion.PathType].NonInitMem() && s.pathPool[epic.PathType].NonInitMem()
		// @ fold s.InitPathPool()
	}
}

// getPath returns a new or recycled path for pathType
// @ requires s.InitPathPool()
// @ ensures  res != nil && err == nil
// @ ensures  pathType == 0 ==> (typeOf(res) == type[empty.Path] && s.InitPathPool())
// @ ensures  0 < pathType  ==> (
// @ 	res.NonInitMem() &&
// @ 	s.InitPathPoolExceptOne(pathType))
// @ decreases
func (s *SCION) getPath(pathType path.Type) (res path.Path, err error) {
	// (VerifiedSCION) Gobra cannot establish this atm, but must hold because
	//                 path.Type is defined as an uint8.
	// @ assume 0 <= pathType
	// @ unfold s.InitPathPool()
	if s.pathPool == nil {
		// @ def.Unreachable()
		return path.NewPath(pathType)
	}
	if int(pathType) < len(s.pathPool) {
		tmp := s.pathPool[pathType]
		// @ ghost if 0 < pathType {
		// @ 	fold   s.InitPathPoolExceptOne(pathType)
		// @ 	assert tmp.NonInitMem()
		// @ } else {
		// @ 	fold s.InitPathPool()
		// @ }
		return tmp, nil
	}
	tmp := s.pathPoolRaw
	// @ fold   s.InitPathPoolExceptOne(pathType)
	// @ assert tmp.NonInitMem()
	return tmp, nil
}

// @ trusted
// @ requires false
func decodeSCION(data []byte, pb gopacket.PacketBuilder) error {
	scn := &SCION{}
	err := scn.DecodeFromBytes(data, pb)
	if err != nil {
		return err
	}
	pb.AddLayer(scn)
	pb.SetNetworkLayer(scn)
	return pb.NextDecoder(scionNextLayerType(scn.NextHdr))
}

// scionNextLayerType returns the layer type for the given protocol identifier
// in a SCION base header.
// @ decreases
func scionNextLayerType(t L4ProtocolType) gopacket.LayerType {
	switch t {
	case HopByHopClass:
		return LayerTypeHopByHopExtn
	case End2EndClass:
		return LayerTypeEndToEndExtn
	default:
		return scionNextLayerTypeL4(t)
	}
}

// scionNextLayerTypeAfterHBH returns the layer type for the given protocol
// identifier in a SCION hop-by-hop extension, excluding (repeated) hop-by-hop
// extensions.
// @ decreases
func scionNextLayerTypeAfterHBH(t L4ProtocolType) gopacket.LayerType {
	switch t {
	case HopByHopClass:
		return gopacket.LayerTypeDecodeFailure
	case End2EndClass:
		return LayerTypeEndToEndExtn
	default:
		return scionNextLayerTypeL4(t)
	}
}

// scionNextLayerTypeAfterE2E returns the layer type for the given protocol
// identifier, in a SCION end-to-end extension, excluding (repeated or
// misordered) hop-by-hop extensions or (repeated) end-to-end extensions.
// @ decreases
func scionNextLayerTypeAfterE2E(t L4ProtocolType) gopacket.LayerType {
	switch t {
	case HopByHopClass:
		return gopacket.LayerTypeDecodeFailure
	case End2EndClass:
		return gopacket.LayerTypeDecodeFailure
	default:
		return scionNextLayerTypeL4(t)
	}
}

// scionNextLayerTypeL4 returns the layer type for the given layer-4 protocol identifier.
// Does not handle extension header classes.
// @ decreases
func scionNextLayerTypeL4(t L4ProtocolType) gopacket.LayerType {
	switch t {
	case L4UDP:
		return LayerTypeSCIONUDP
	case L4SCMP:
		return LayerTypeSCMP
	case L4BFD:
		return layerTypeBFD
	default:
		return gopacket.LayerTypePayload
	}
}

// DstAddr parses the destination address into a net.Addr. The returned net.Addr references data
// from the underlaying layer data. Changing the net.Addr object might lead to inconsistent layer
// information and thus should be treated read-only. Instead, SetDstAddr should be used to update
// the destination address.
// @ trusted
// @ requires false
func (s *SCION) DstAddr() (net.Addr, error) {
	return parseAddr(s.DstAddrType, s.RawDstAddr)
}

// SrcAddr parses the source address into a net.Addr. The returned net.Addr references data from the
// underlaying layer data. Changing the net.Addr object might lead to inconsistent layer information
// and thus should be treated read-only. Instead, SetDstAddr should be used to update the source
// address.
// @ trusted
// @ requires false
func (s *SCION) SrcAddr() (net.Addr, error) {
	return parseAddr(s.SrcAddrType, s.RawSrcAddr)
}

// SetDstAddr sets the destination address and updates the DstAddrType field accordingly.
// SetDstAddr takes ownership of dst and callers should not write to it after calling SetDstAddr.
// Changes to dst might leave the layer in an inconsistent state.
// @ trusted
// @ requires false
func (s *SCION) SetDstAddr(dst net.Addr) error {
	var err error
	s.DstAddrType, s.RawDstAddr, err = packAddr(dst)
	return err
}

// SetSrcAddr sets the source address and updates the DstAddrType field accordingly.
// SetSrcAddr takes ownership of src and callers should not write to it after calling SetSrcAddr.
// Changes to src might leave the layer in an inconsistent state.
// @ trusted
// @ requires false
func (s *SCION) SetSrcAddr(src net.Addr) error {
	var err error
	s.SrcAddrType, s.RawSrcAddr, err = packAddr(src)
	return err
}

// @ trusted
// @ requires false
func parseAddr(addrType AddrType, raw []byte) (net.Addr, error) {
	switch addrType {
	case T4Ip:
		return &net.IPAddr{IP: net.IP(raw)}, nil
	case T4Svc:
		return addr.HostSVC(binary.BigEndian.Uint16(raw[:addr.HostLenSVC])), nil
	case T16Ip:
		return &net.IPAddr{IP: net.IP(raw)}, nil
	}
	return nil, serrors.New("unsupported address type/length combination",
		"type", addrType, "len", addrType.Length())
}

// @ trusted
// @ requires false
func packAddr(hostAddr net.Addr) (AddrType, []byte, error) {
	switch a := hostAddr.(type) {
	case *net.IPAddr:
		if ip := a.IP.To4(); ip != nil {
			return T4Ip, ip, nil
		}
		return T16Ip, a.IP, nil
	case addr.HostSVC:
		return T4Svc, a.PackWithPad(2), nil
	}
	return 0, nil, serrors.New("unsupported address", "addr", hostAddr)
}

// AddrHdrLen returns the length of the address header (destination and source ISD-AS-Host triples)
// in bytes.
//
//	(VerifiedSCION):
//	AddrHdrLen is meant to be called both inside and outside slayers.
//	To enforce abstraction, we introduce a second field `insideSlayers`
//	in order to chose between the appropriate contract for this method.
//	This hack will not be needed when we introduce support for
//	multiple contracts per method.
//
// @ pure
// @ requires insideSlayers ==> (acc(&s.DstAddrType, def.ReadL20) && acc(&s.SrcAddrType, def.ReadL20))
// @ requires insideSlayers ==> s.DstAddrType.Has3Bits() && s.SrcAddrType.Has3Bits()
// @ requires !insideSlayers ==> acc(s.Mem(ubuf), _)
// @ ensures  insideSlayers  ==> res == s.addrHdrLenAbstractionLeak()
// @ ensures  !insideSlayers ==> res == s.AddrHdrLenNoAbstractionLeak(ubuf)
// @ ensures  0 <= res
// @ decreases
// @ trusted
func (s *SCION) AddrHdrLen( /*@ ghost ubuf []byte, ghost insideSlayers bool @*/ ) (res int) {
	return 2*addr.IABytes + s.DstAddrType.Length() + s.SrcAddrType.Length()
}

// SerializeAddrHdr serializes destination and source ISD-AS-Host address triples into the provided
// buffer. The caller must ensure that the correct address types and lengths are set in the SCION
// layer, otherwise the results of this method are undefined.
// @ preserves acc(s.HeaderMem(ubuf), def.ReadL10)
// @ preserves sl.AbsSlice_Bytes(buf, 0, len(buf))
// @ preserves sl.AbsSlice_Bytes(ubuf, 0, len(ubuf))
// @ decreases
func (s *SCION) SerializeAddrHdr(buf []byte /*@ , ghost ubuf []byte @*/) error {
	// @ unfold acc(s.HeaderMem(ubuf), def.ReadL10)
	// @ defer fold acc(s.HeaderMem(ubuf), def.ReadL10)
	if len(buf) < s.AddrHdrLen( /*@ nil, true @*/ ) {
		return serrors.New("provided buffer is too small", "expected", s.AddrHdrLen( /*@ nil, true @*/ ),
			"actual", len(buf))
	}
	dstAddrBytes := s.DstAddrType.Length()
	srcAddrBytes := s.SrcAddrType.Length()
	offset := 0
	// @ sl.SplitRange_Bytes(buf, offset, len(buf), writePerm)
	// @ unfold sl.AbsSlice_Bytes(buf[offset:], 0, len(buf[offset:]))
	binary.BigEndian.PutUint64(buf[offset:], uint64(s.DstIA))
	// @ fold sl.AbsSlice_Bytes(buf[offset:], 0, len(buf[offset:]))
	// @ sl.CombineRange_Bytes(buf, offset, len(buf), writePerm)
	offset += addr.IABytes
	// @ sl.SplitRange_Bytes(buf, offset, len(buf), writePerm)
	// @ unfold sl.AbsSlice_Bytes(buf[offset:], 0, len(buf[offset:]))
	binary.BigEndian.PutUint64(buf[offset:], uint64(s.SrcIA))
	// @ fold sl.AbsSlice_Bytes(buf[offset:], 0, len(buf[offset:]))
	// @ sl.CombineRange_Bytes(buf, offset, len(buf), writePerm)
	offset += addr.IABytes
	// @ sl.SplitRange_Bytes(buf, offset, offset+dstAddrBytes, writePerm)
	// @ sl.SplitRange_Bytes(ubuf, offset, offset+dstAddrBytes, writePerm)

	// @ unfold sl.AbsSlice_Bytes(buf[offset:offset+dstAddrBytes], 0, len(buf[offset:offset+dstAddrBytes]))
	// @ unfold sl.AbsSlice_Bytes(ubuf[offset:offset+dstAddrBytes], 0, len(ubuf[offset:offset+dstAddrBytes]))
	copy(buf[offset:offset+dstAddrBytes], s.RawDstAddr /*@ , def.ReadL10 @*/)
	// @ fold sl.AbsSlice_Bytes(buf[offset:offset+dstAddrBytes], 0, len(buf[offset:offset+dstAddrBytes]))
	// @ fold sl.AbsSlice_Bytes(ubuf[offset:offset+dstAddrBytes], 0, len(ubuf[offset:offset+dstAddrBytes]))
	// @ sl.CombineRange_Bytes(buf, offset, offset+dstAddrBytes, writePerm)
	// @ sl.CombineRange_Bytes(ubuf, offset, offset+dstAddrBytes, writePerm)

	offset += dstAddrBytes
	// @ sl.SplitRange_Bytes(buf, offset, offset+srcAddrBytes, writePerm)
	// @ sl.SplitRange_Bytes(ubuf, offset, offset+srcAddrBytes, writePerm)

	// @ unfold sl.AbsSlice_Bytes(buf[offset:offset+srcAddrBytes], 0, len(buf[offset:offset+srcAddrBytes]))
	// @ unfold sl.AbsSlice_Bytes(ubuf[offset:offset+srcAddrBytes], 0, len(ubuf[offset:offset+srcAddrBytes]))

	copy(buf[offset:offset+srcAddrBytes], s.RawSrcAddr /*@ , def.ReadL10 @*/)

	// @ fold sl.AbsSlice_Bytes(buf[offset:offset+srcAddrBytes], 0, len(buf[offset:offset+srcAddrBytes]))
	// @ fold sl.AbsSlice_Bytes(ubuf[offset:offset+srcAddrBytes], 0, len(ubuf[offset:offset+srcAddrBytes]))
	// @ sl.CombineRange_Bytes(buf, offset, offset+srcAddrBytes, writePerm)
	// @ sl.CombineRange_Bytes(ubuf, offset, offset+srcAddrBytes, writePerm)

	return nil
}

// DecodeAddrHdr decodes the destination and source ISD-AS-Host address triples from the provided
// buffer. The caller must ensure that the correct address types and lengths are set in the SCION
// layer, otherwise the results of this method are undefined.
// @ requires  acc(&s.SrcIA) && acc(&s.DstIA)
// @ requires  acc(&s.SrcAddrType, def.ReadL1) && s.SrcAddrType.Has3Bits()
// @ requires  acc(&s.DstAddrType, def.ReadL1) && s.DstAddrType.Has3Bits()
// @ requires  acc(&s.RawSrcAddr) && acc(&s.RawDstAddr)
// @ preserves acc(sl.AbsSlice_Bytes(data, 0, len(data)), def.ReadL10)
// @ ensures   res == nil ==> s.HeaderMem(data)
// @ ensures   res != nil ==> res.ErrorMem()
// @ ensures   res != nil ==> (
// @	acc(&s.SrcIA) && acc(&s.DstIA) &&
// @ 	acc(&s.SrcAddrType, def.ReadL1) && acc(&s.DstAddrType, def.ReadL1) &&
// @ 	acc(&s.RawSrcAddr) && acc(&s.RawDstAddr))
// @ decreases
func (s *SCION) DecodeAddrHdr(data []byte) (res error) {
	// @ ghost l := s.AddrHdrLen(nil, true)
	if len(data) < s.AddrHdrLen( /*@ nil, true @*/ ) {
		return serrors.New("provided buffer is too small", "expected", s.AddrHdrLen( /*@ nil, true @*/ ),
			"actual", len(data))
	}
	offset := 0
	// @ unfold acc(sl.AbsSlice_Bytes(data, 0, len(data)), def.ReadL10)
	// @ assert forall i int :: { &data[offset:][i] }{ &data[i] } 0 <= i && i < l ==> &data[offset:][i] == &data[i]
	s.DstIA = addr.IA(binary.BigEndian.Uint64(data[offset:]))
	offset += addr.IABytes
	// @ assert forall i int :: { &data[offset:][i] } 0 <= i && i < l ==> &data[offset:][i] == &data[offset+i]
	s.SrcIA = addr.IA(binary.BigEndian.Uint64(data[offset:]))
	// @ fold acc(sl.AbsSlice_Bytes(data, 0, len(data)), def.ReadL10)
	offset += addr.IABytes
	dstAddrBytes := s.DstAddrType.Length()
	srcAddrBytes := s.SrcAddrType.Length()
	s.RawDstAddr = data[offset : offset+dstAddrBytes]
	offset += dstAddrBytes
	s.RawSrcAddr = data[offset : offset+srcAddrBytes]
	// @ fold s.HeaderMem(data)

	return nil
}

// computeChecksum computes the checksum with the SCION pseudo header.
// @ requires  acc(&s.RawSrcAddr, def.ReadL20) && acc(&s.RawDstAddr, def.ReadL20)
// @ requires  len(s.RawSrcAddr) % 2 == 0 && len(s.RawDstAddr) % 2 == 0
// @ requires  acc(&s.SrcIA, def.ReadL20) && acc(&s.DstIA, def.ReadL20)
// @ requires  acc(sl.AbsSlice_Bytes(s.RawSrcAddr, 0, len(s.RawSrcAddr)), def.ReadL20)
// @ requires  acc(sl.AbsSlice_Bytes(s.RawDstAddr, 0, len(s.RawDstAddr)), def.ReadL20)
// @ preserves acc(sl.AbsSlice_Bytes(upperLayer, 0, len(upperLayer)), def.ReadL20)
// @ ensures   acc(&s.RawSrcAddr, def.ReadL20) && acc(&s.RawDstAddr, def.ReadL20)
// @ ensures   acc(&s.SrcIA, def.ReadL20) && acc(&s.DstIA, def.ReadL20)
// @ ensures   acc(sl.AbsSlice_Bytes(s.RawSrcAddr, 0, len(s.RawSrcAddr)), def.ReadL20)
// @ ensures   acc(sl.AbsSlice_Bytes(s.RawDstAddr, 0, len(s.RawDstAddr)), def.ReadL20)
// @ ensures   s == nil ==> err != nil
// @ ensures   len(s.RawDstAddr) == 0 ==> err != nil
// @ ensures   len(s.RawSrcAddr) == 0 ==> err != nil
// @ ensures   err != nil ==> err.ErrorMem()
// @ ensures   len(s.RawDstAddr) > 0 && len(s.RawSrcAddr) > 0 ==> err == nil
// @ decreases
func (s *SCION) computeChecksum(upperLayer []byte, protocol uint8) (res uint16, err error) {
	if s == nil {
		return 0, serrors.New("SCION header missing")
	}
	csum, err := s.pseudoHeaderChecksum(len(upperLayer), protocol)
	if err != nil {
		return 0, err
	}
	csum = s.upperLayerChecksum(upperLayer, csum)
	folded := s.foldChecksum(csum)
	return folded, nil
}

// @ requires acc(&s.RawSrcAddr, def.ReadL20) && acc(&s.RawDstAddr, def.ReadL20)
// @ requires len(s.RawSrcAddr) % 2 == 0 && len(s.RawDstAddr) % 2 == 0
// @ requires acc(&s.SrcIA, def.ReadL20) && acc(&s.DstIA, def.ReadL20)
// @ requires acc(sl.AbsSlice_Bytes(s.RawSrcAddr, 0, len(s.RawSrcAddr)), def.ReadL20)
// @ requires acc(sl.AbsSlice_Bytes(s.RawDstAddr, 0, len(s.RawDstAddr)), def.ReadL20)
// @ ensures  acc(&s.RawSrcAddr, def.ReadL20) && acc(&s.RawDstAddr, def.ReadL20)
// @ ensures  acc(&s.SrcIA, def.ReadL20) && acc(&s.DstIA, def.ReadL20)
// @ ensures  acc(sl.AbsSlice_Bytes(s.RawSrcAddr, 0, len(s.RawSrcAddr)), def.ReadL20)
// @ ensures  acc(sl.AbsSlice_Bytes(s.RawDstAddr, 0, len(s.RawDstAddr)), def.ReadL20)
// @ ensures  len(s.RawDstAddr) == 0 ==> err != nil
// @ ensures  len(s.RawSrcAddr) == 0 ==> err != nil
// @ ensures  err != nil ==> err.ErrorMem()
// @ ensures  len(s.RawDstAddr) > 0 && len(s.RawSrcAddr) > 0 ==> err == nil
// @ decreases
func (s *SCION) pseudoHeaderChecksum(length int, protocol uint8) (res uint32, err error) {
	if len(s.RawDstAddr) == 0 {
		return 0, serrors.New("destination address missing")
	}
	if len(s.RawSrcAddr) == 0 {
		return 0, serrors.New("source address missing")
	}
	var csum uint32
	var srcIA /*@@@*/, dstIA /*@@@*/ [8]byte
	binary.BigEndian.PutUint64(srcIA[:], uint64(s.SrcIA))
	binary.BigEndian.PutUint64(dstIA[:], uint64(s.DstIA))
	// @ invariant forall j int :: { &srcIA[j] } 0 <= j && j < 8 ==> acc(&srcIA[j])
	// @ invariant forall j int :: { &dstIA[j] } 0 <= j && j < 8 ==> acc(&dstIA[j])
	// @ invariant i % 2 == 0
	// @ invariant 0 <= i && i <= 8
	// @ decreases 8 - i
	for i := 0; i < 8; i += 2 {
		csum += uint32(srcIA[i]) << 8
		csum += uint32(srcIA[i+1])
		csum += uint32(dstIA[i]) << 8
		csum += uint32(dstIA[i+1])
	}
	// Address length is guaranteed to be a multiple of 2 by the protocol.
	// @ ghost var rawSrcAddrLen int = len(s.RawSrcAddr)
	// @ invariant acc(&s.RawSrcAddr, def.ReadL20) && acc(sl.AbsSlice_Bytes(s.RawSrcAddr, 0, len(s.RawSrcAddr)), def.ReadL20)
	// @ invariant len(s.RawSrcAddr) == rawSrcAddrLen
	// @ invariant len(s.RawSrcAddr) % 2 == 0
	// @ invariant i % 2 == 0
	// @ invariant 0 <= i && i <= len(s.RawSrcAddr)
	// @ decreases len(s.RawSrcAddr) - i
	for i := 0; i < len(s.RawSrcAddr); i += 2 {
		// @ preserves err == nil
		// @ requires acc(&s.RawSrcAddr, def.ReadL20) && acc(sl.AbsSlice_Bytes(s.RawSrcAddr, 0, len(s.RawSrcAddr)), def.ReadL20)
		// @ requires 0 <= i && i < len(s.RawSrcAddr) && i % 2 == 0 && len(s.RawSrcAddr) % 2 == 0
		// @ ensures acc(&s.RawSrcAddr, def.ReadL20) && acc(sl.AbsSlice_Bytes(s.RawSrcAddr, 0, len(s.RawSrcAddr)), def.ReadL20)
		// @ ensures s.RawSrcAddr === before(s.RawSrcAddr)
		// @ decreases
		// @ outline(
		// @ unfold acc(sl.AbsSlice_Bytes(s.RawSrcAddr, 0, len(s.RawSrcAddr)), def.ReadL20)
		csum += uint32(s.RawSrcAddr[i]) << 8
		csum += uint32(s.RawSrcAddr[i+1])
		// @ fold acc(sl.AbsSlice_Bytes(s.RawSrcAddr, 0, len(s.RawSrcAddr)), def.ReadL20)
		// @ )
	}
	// @ ghost var rawDstAddrLen int = len(s.RawDstAddr)
	// @ invariant acc(&s.RawDstAddr, def.ReadL20) && acc(sl.AbsSlice_Bytes(s.RawDstAddr, 0, len(s.RawDstAddr)), def.ReadL20)
	// @ invariant len(s.RawDstAddr) == rawDstAddrLen
	// @ invariant len(s.RawDstAddr) % 2 == 0
	// @ invariant i % 2 == 0
	// @ invariant 0 <= i && i <= len(s.RawDstAddr)
	// @ decreases len(s.RawDstAddr) - i
	for i := 0; i < len(s.RawDstAddr); i += 2 {
		// @ preserves err == nil
		// @ requires acc(&s.RawDstAddr, def.ReadL20) && acc(sl.AbsSlice_Bytes(s.RawDstAddr, 0, len(s.RawDstAddr)), def.ReadL20)
		// @ requires 0 <= i && i < len(s.RawDstAddr) && i % 2 == 0 && len(s.RawDstAddr) % 2 == 0
		// @ ensures acc(&s.RawDstAddr, def.ReadL20) && acc(sl.AbsSlice_Bytes(s.RawDstAddr, 0, len(s.RawDstAddr)), def.ReadL20)
		// @ ensures s.RawDstAddr === before(s.RawDstAddr)
		// @ decreases
		// @ outline(
		// @ unfold acc(sl.AbsSlice_Bytes(s.RawDstAddr, 0, len(s.RawDstAddr)), def.ReadL20)
		csum += uint32(s.RawDstAddr[i]) << 8
		csum += uint32(s.RawDstAddr[i+1])
		// @ fold acc(sl.AbsSlice_Bytes(s.RawDstAddr, 0, len(s.RawDstAddr)), def.ReadL20)
		// @ )
	}
	l := uint32(length)
	csum += (l >> 16) + (l & 0xffff)
	csum += uint32(protocol)
	return csum, nil
}

// @ preserves acc(sl.AbsSlice_Bytes(upperLayer, 0, len(upperLayer)), def.ReadL20)
// @ decreases
func (s *SCION) upperLayerChecksum(upperLayer []byte, csum uint32) uint32 {
	// Compute safe boundary to ensure we do not access out of bounds.
	// Odd lengths are handled at the end.
	safeBoundary := len(upperLayer) - 1
	// @ unfold acc(sl.AbsSlice_Bytes(upperLayer, 0, len(upperLayer)), def.ReadL20)
	// @ invariant 0 <= i && i < safeBoundary + 2
	// @ invariant i % 2 == 0
	// @ invariant forall i int :: 0 <= i && i < len(upperLayer) ==> acc(&upperLayer[i], def.ReadL20)
	// @ decreases safeBoundary - i
	for i := 0; i < safeBoundary; i += 2 {
		csum += uint32(upperLayer[i]) << 8
		csum += uint32(upperLayer[i+1])
	}
	if len(upperLayer)%2 == 1 {
		csum += uint32(upperLayer[safeBoundary]) << 8
	}
	// @ fold acc(sl.AbsSlice_Bytes(upperLayer, 0, len(upperLayer)), def.ReadL20)
	return csum
}

// (VerifiedSCION) The following function terminates but Gobra can't
// deduce that because of limited support of bitwise operations.
// @ decreases _
func (s *SCION) foldChecksum(csum uint32) (res uint16) {
	for csum > 0xffff {
		csum = (csum >> 16) + (csum & 0xffff)
	}
	return ^uint16(csum)
}
