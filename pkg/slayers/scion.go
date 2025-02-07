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
	"net/netip"

	"github.com/gopacket/gopacket"

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
	// @ . "github.com/scionproto/scion/verification/utils/definitions"
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
// @ pure
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
// @ requires false
func (b *BaseLayer) LayerContents() (res []byte) {
	res = b.Contents
	return res
}

// LayerPayload returns the bytes contained within the packet layer.
// @ preserves acc(b.Mem(ub, bp), R20)
// @ ensures   len(res) == len(ub) - bp
// @ ensures   0 <= bp && bp <= len(ub)
// @ ensures   res === ub[bp:]
// @ decreases
func (b *BaseLayer) LayerPayload( /*@ ghost ub []byte, ghost bp int @*/ ) (res []byte) {
	// @ unfold acc(b.Mem(ub, bp), R20)
	res = b.Payload
	// @ fold acc(b.Mem(ub, bp), R20)
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

// @ ensures res != nil && res === LayerClassSCION
// @ ensures typeOf(res) == gopacket.LayerType
// @ decreases
func (s *SCION) CanDecode() (res gopacket.LayerClass) {
	res = LayerClassSCION
	// @ LayerClassSCIONIsLayerType()
	return res
}

// @ preserves acc(s.Mem(ub), R20)
// @ decreases
func (s *SCION) NextLayerType( /*@ ghost ub []byte @*/ ) gopacket.LayerType {
	return scionNextLayerType( /*@ unfolding acc(s.Mem(ub), R20) in @*/ s.NextHdr)
}

// @ preserves acc(s.Mem(ub), R20)
// @ ensures   0 <= start && start <= end && end <= len(ub)
// @ ensures   len(res) == end - start
// @ ensures   res === ub[start:end]
// @ decreases
func (s *SCION) LayerPayload( /*@ ghost ub []byte @*/ ) (res []byte /*@ , ghost start int, ghost end int @*/) {
	//@ unfold acc(s.Mem(ub), R20)
	res = s.Payload
	//@ start = int(s.HdrLen*LineLen)
	//@ end = len(ub)
	//@ fold acc(s.Mem(ub), R20)
	return res /*@, start, end @*/
}

// @ ensures res == gopacket.Flow{}
// @ decreases
func (s *SCION) NetworkFlow() (res gopacket.Flow) {
	// TODO(shitz): Investigate how we can use gopacket.Flow.
	return gopacket.Flow{}
}

// @ requires  !opts.FixLengths
// @ requires  b != nil && b.Mem()
// @ requires  acc(s.Mem(ubuf), R0)
// @ requires  sl.Bytes(ubuf, 0, len(ubuf))
// @ requires  sl.Bytes(b.UBuf(), 0, len(b.UBuf()))
// @ ensures   b.Mem()
// @ ensures   acc(s.Mem(ubuf), R0)
// @ ensures   sl.Bytes(ubuf, 0, len(ubuf))
// @ ensures   sl.Bytes(b.UBuf(), 0, len(b.UBuf()))
// @ ensures   e == nil && s.HasOneHopPath(ubuf) ==>
// @ 	len(b.UBuf()) == old(len(b.UBuf())) + s.MinSizeOfUbufWithOneHop(ubuf)
// @ ensures   e != nil ==> e.ErrorMem()
// post for IO:
// @ ensures   e == nil && old(s.EqPathType(ubuf)) ==>
// @ 	IsSupportedRawPkt(b.View()) == old(IsSupportedPkt(ubuf))
// @ decreases
func (s *SCION) SerializeTo(b gopacket.SerializeBuffer, opts gopacket.SerializeOptions /* @ , ghost ubuf []byte @*/) (e error) {
	// @ unfold acc(s.Mem(ubuf), R1)
	// @ defer fold acc(s.Mem(ubuf), R1)
	// @ sl.SplitRange_Bytes(ubuf, int(CmnHdrLen+s.AddrHdrLen(nil, true)), int(s.HdrLen*LineLen), R10)
	scnLen := CmnHdrLen + s.AddrHdrLen( /*@ nil, true @*/ ) + s.Path.Len( /*@ ubuf[CmnHdrLen+s.AddrHdrLen(nil, true) : s.HdrLen*LineLen] @*/ )
	// @ sl.CombineRange_Bytes(ubuf, int(CmnHdrLen+s.AddrHdrLenSpecInternal()), int(s.HdrLen*LineLen), R10)
	if scnLen > MaxHdrLen {
		return serrors.New("header length exceeds maximum",
			"max", MaxHdrLen, "actual", scnLen)
	}
	if scnLen%LineLen != 0 {
		return serrors.New("header length is not an integer multiple of line length",
			"actual", scnLen)
	}
	buf, err := b.PrependBytes(scnLen)
	if err != nil {
		return err
	}
	if opts.FixLengths {
		// @ Unreachable()
		s.HdrLen = uint8(scnLen / LineLen)
		s.PayloadLen = uint16(len(b.Bytes()) - scnLen)
	}
	// @ ghost uSerBufN := b.UBuf()
	// @ assert buf === uSerBufN[:scnLen]

	// @ unfold acc(sl.Bytes(uSerBufN, 0, len(uSerBufN)), writePerm)
	// Serialize common header.
	firstLine := uint32(s.Version&0xF)<<28 | uint32(s.TrafficClass)<<20 | s.FlowID&0xFFFFF
	binary.BigEndian.PutUint32(buf[:4], firstLine)
	buf[4] = uint8(s.NextHdr)
	buf[5] = s.HdrLen
	// @ assert &buf[6:8][0] == &buf[6] && &buf[6:8][1] == &buf[7]
	binary.BigEndian.PutUint16(buf[6:8], s.PayloadLen)
	buf[8] = uint8(s.PathType)
	buf[9] = uint8(s.DstAddrType&0xF)<<4 | uint8(s.SrcAddrType&0xF)
	binary.BigEndian.PutUint16(buf[10:12], 0)
	// @ fold acc(sl.Bytes(uSerBufN, 0, len(uSerBufN)), writePerm)
	// @ ghost if s.EqPathType(ubuf) {
	// @ 	assert reveal s.EqPathTypeWithBuffer(ubuf, uSerBufN)
	// @ 	s.IsSupportedPktLemma(ubuf, uSerBufN)
	// @ }

	// Serialize address header.
	// @ sl.SplitRange_Bytes(uSerBufN, CmnHdrLen, scnLen, HalfPerm)
	// @ sl.Reslice_Bytes(uSerBufN, 0, CmnHdrLen, R54)
	// @ IsSupportedPktSubslice(uSerBufN, CmnHdrLen)
	// @ sl.SplitRange_Bytes(uSerBufN, CmnHdrLen, scnLen, HalfPerm)
	// @ sl.SplitRange_Bytes(ubuf, CmnHdrLen, len(ubuf), R10)
	if err := s.SerializeAddrHdr(buf[CmnHdrLen:] /*@ , ubuf[CmnHdrLen:] @*/); err != nil {
		// @ sl.Unslice_Bytes(uSerBufN, 0, CmnHdrLen, R54)
		// @ sl.CombineRange_Bytes(uSerBufN, CmnHdrLen, scnLen, writePerm)
		// @ sl.CombineRange_Bytes(ubuf, CmnHdrLen, len(ubuf), R10)
		return err
	}
	offset := CmnHdrLen + s.AddrHdrLen( /*@ nil, true @*/ )

	// @ sl.CombineRange_Bytes(uSerBufN, CmnHdrLen, scnLen, HalfPerm)
	// @ sl.CombineRange_Bytes(ubuf, CmnHdrLen, len(ubuf), R10)
	// @ IsSupportedPktSubslice(uSerBufN, CmnHdrLen)
	// @ sl.Unslice_Bytes(uSerBufN, 0, CmnHdrLen, R54)
	// @ sl.CombineRange_Bytes(uSerBufN, CmnHdrLen, scnLen, HalfPerm)

	// Serialize path header.
	// @ ghost startP := int(CmnHdrLen+s.AddrHdrLenSpecInternal())
	// @ ghost endP := int(s.HdrLen*LineLen)
	// @ ghost pathSlice := ubuf[startP : endP]
	// @ sl.SplitRange_Bytes(uSerBufN, offset, scnLen, HalfPerm)
	// @ sl.SplitRange_Bytes(ubuf, startP, endP, HalfPerm)
	// @ sl.Reslice_Bytes(uSerBufN, 0, offset, R54)
	// @ sl.Reslice_Bytes(ubuf, 0, startP, R54)
	// @ IsSupportedPktSubslice(uSerBufN, offset)
	// @ IsSupportedPktSubslice(ubuf, startP)
	// @ sl.SplitRange_Bytes(uSerBufN, offset, scnLen, HalfPerm)
	// @ sl.SplitRange_Bytes(ubuf, startP, endP, HalfPerm)
	tmp := s.Path.SerializeTo(buf[offset:] /*@, pathSlice @*/)
	// @ sl.CombineRange_Bytes(uSerBufN, offset, scnLen, HalfPerm)
	// @ sl.CombineRange_Bytes(ubuf, startP, endP, HalfPerm)
	// @ IsSupportedPktSubslice(uSerBufN, offset)
	// @ IsSupportedPktSubslice(ubuf, startP)
	// @ sl.Unslice_Bytes(uSerBufN, 0, offset, R54)
	// @ sl.Unslice_Bytes(ubuf, 0, startP, R54)
	// @ sl.CombineRange_Bytes(uSerBufN, offset, scnLen, HalfPerm)
	// @ sl.CombineRange_Bytes(ubuf, startP, endP, HalfPerm)
	// @ reveal IsSupportedPkt(uSerBufN)
	// @ reveal IsSupportedRawPkt(b.View())
	return tmp
}

// DecodeFromBytes decodes the SCION layer. DecodeFromBytes resets the internal state of this layer
// to the state defined by the passed-in bytes. Slices in the SCION layer reference the passed-in
// data, so care should be taken to copy it first should later modification of data be required
// before the SCION layer is discarded.
// @ requires  s.NonInitMem()
// @ preserves acc(sl.Bytes(data, 0, len(data)), R40)
// @ preserves df != nil && df.Mem()
// @ ensures   res == nil ==> s.Mem(data)
// @ ensures   res == nil && typeOf(s.GetPath(data)) == *scion.Raw ==>
// @ 	s.EqAbsHeader(data) && s.ValidScionInitSpec(data)
// @ ensures   res == nil ==> s.EqPathType(data)
// @ ensures   res != nil ==> s.NonInitMem() && res.ErrorMem()
// @ decreases
func (s *SCION) DecodeFromBytes(data []byte, df gopacket.DecodeFeedback) (res error) {
	// Decode common header.
	if len(data) < CmnHdrLen {
		df.SetTruncated()
		return serrors.New("packet is shorter than the common header length",
			"min", CmnHdrLen, "actual", len(data))
	}
	// @ sl.SplitRange_Bytes(data, 0, 4, R41)
	// @ preserves 4 <= len(data) && acc(sl.Bytes(data[:4], 0, 4), R41)
	// @ decreases
	// @ outline(
	// @ unfold acc(sl.Bytes(data[:4], 0, 4), R41)
	firstLine := binary.BigEndian.Uint32(data[:4])
	// @ fold acc(sl.Bytes(data[:4], 0, 4), R41)
	// @ )
	// @ sl.CombineRange_Bytes(data, 0, 4, R41)
	// @ unfold s.NonInitMem()
	s.Version = uint8(firstLine >> 28)
	s.TrafficClass = uint8((firstLine >> 20) & 0xFF)
	s.FlowID = firstLine & 0xFFFFF
	// @ preserves acc(&s.NextHdr) && acc(&s.HdrLen) && acc(&s.PayloadLen) && acc(&s.PathType)
	// @ preserves acc(&s.DstAddrType) && acc(&s.SrcAddrType)
	// @ preserves CmnHdrLen <= len(data) && acc(sl.Bytes(data, 0, len(data)), R41)
	// @ ensures   s.DstAddrType.Has3Bits() && s.SrcAddrType.Has3Bits()
	// @ ensures   0 <= s.PathType && s.PathType < 256
	// @ ensures   path.Type(GetPathType(data)) == s.PathType
	// @ ensures   L4ProtocolType(GetNextHdr(data)) == s.NextHdr
	// @ ensures   GetLength(data) == int(s.HdrLen * LineLen)
	// @ ensures   GetAddressOffset(data) ==
	// @	CmnHdrLen + 2*addr.IABytes + s.DstAddrType.Length() + s.SrcAddrType.Length()
	// @ decreases
	// @ outline(
	// @ unfold acc(sl.Bytes(data, 0, len(data)), R41)
	s.NextHdr = L4ProtocolType(data[4])
	s.HdrLen = data[5]
	// @ assert &data[6:8][0] == &data[6] && &data[6:8][1] == &data[7]
	s.PayloadLen = binary.BigEndian.Uint16(data[6:8])
	// @ b.ByteValue(data[8])
	s.PathType = path.Type(data[8])
	s.DstAddrType = AddrType(data[9] >> 4 & 0xF)
	s.SrcAddrType = AddrType(data[9] & 0xF)

	// Decode address header.
	// @ sl.SplitByIndex_Bytes(data, 0, len(data), CmnHdrLen, R41)
	// @ sl.Reslice_Bytes(data, CmnHdrLen, len(data), R41)
	if err := s.DecodeAddrHdr(data[CmnHdrLen:]); err != nil {
		// @ fold s.NonInitMem()
		// @ sl.Unslice_Bytes(data, CmnHdrLen, len(data), R41)
		// @ sl.CombineAtIndex_Bytes(data, 0, len(data), CmnHdrLen, R41)
		df.SetTruncated()
		return err
	}
	// @ sl.Unslice_Bytes(data, CmnHdrLen, len(data), R41)
	// @ sl.CombineAtIndex_Bytes(data, 0, len(data), CmnHdrLen, R41)
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

	// @ assert unfolding PathPoolMem(s.pathPool, s.pathPoolRaw) in (s.pathPool == nil) == (s.pathPoolRaw == nil)
	s.Path, err = s.getPath(s.PathType)
	if err != nil {
		// @ unfold s.HeaderMem(data[CmnHdrLen:])
		// @ fold s.NonInitMem()
		return err
	}
	// @ sl.SplitRange_Bytes(data, offset, offset+pathLen, R41)
	err = s.Path.DecodeFromBytes(data[offset : offset+pathLen])
	if err != nil {
		// @ sl.CombineRange_Bytes(data, offset, offset+pathLen, R41)
		// @ unfold s.HeaderMem(data[CmnHdrLen:])
		// @ s.PathPoolMemExchange(s.PathType, s.Path)
		// @ fold s.NonInitMem()
		return err
	}
	// @ ghost if typeOf(s.Path) == type[*onehop.Path] {
	// @ 	s.Path.(*onehop.Path).InferSizeUb(data[offset : offset+pathLen])
	// @ 	assert s.Path.LenSpec(data[offset : offset+pathLen]) <= len(data[offset : offset+pathLen])
	// @ 	assert CmnHdrLen + s.AddrHdrLenSpecInternal() + s.Path.LenSpec(data[offset : offset+pathLen]) <= len(data)
	// @ }
	s.Contents = data[:hdrBytes]
	s.Payload = data[hdrBytes:]
	// @ fold acc(s.Mem(data), R54)
	// @ ghost if(typeOf(s.GetPath(data)) == (*scion.Raw)) {
	// @ 	unfold acc(sl.Bytes(data, 0, len(data)), R56)
	// @ 	unfold acc(sl.Bytes(data[offset : offset+pathLen], 0, len(data[offset : offset+pathLen])), R56)
	// @ 	unfold acc(s.Path.(*scion.Raw).Mem(data[offset : offset+pathLen]), R55)
	// @ 	assert reveal s.EqAbsHeader(data)
	// @ 	assert reveal s.ValidScionInitSpec(data)
	// @ 	fold acc(s.Path.Mem(data[offset : offset+pathLen]), R55)
	// @ 	fold acc(sl.Bytes(data, 0, len(data)), R56)
	// @ 	fold acc(sl.Bytes(data[offset : offset+pathLen], 0, len(data[offset : offset+pathLen])), R56)
	// @ }
	// @ sl.CombineRange_Bytes(data, offset, offset+pathLen, R41)
	// @ assert typeOf(s.GetPath(data)) == *scion.Raw ==> s.EqAbsHeader(data) && s.ValidScionInitSpec(data)
	// @ assert reveal s.EqPathType(data)
	// @ fold acc(s.Mem(data), 1-R54)
	return nil
}

// RecyclePaths enables recycling of paths used for DecodeFromBytes. This is
// only useful if the layer itself is reused.
// When this is enabled, the Path instance may be overwritten in
// DecodeFromBytes. No references to Path should be kept in use between
// invocations of DecodeFromBytes.
// @ preserves acc(&s.pathPool) && acc(&s.pathPoolRaw)
// @ preserves PathPoolMem(s.pathPool, s.pathPoolRaw)
// @ ensures   s.pathPoolInitialized()
// @ decreases
func (s *SCION) RecyclePaths() {
	// @ unfold PathPoolMem(s.pathPool, s.pathPoolRaw)
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
		// @ fold s.pathPool[empty.PathType].NonInitMem()
	}
	// @ fold PathPoolMem(s.pathPool, s.pathPoolRaw)
}

// getPath returns a new or recycled path for pathType
// @ requires  acc(&s.pathPool, R20) && acc(&s.pathPoolRaw, R20)
// @ requires  PathPoolMem(s.pathPool, s.pathPoolRaw)
// @ requires  0 <= pathType && pathType < path.MaxPathType
// @ ensures   acc(&s.pathPool, R20) && acc(&s.pathPoolRaw, R20)
// @ ensures   err == nil ==> res != nil
// @ ensures   err == nil ==> res.NonInitMem()
// @ ensures   (err == nil && !s.pathPoolInitialized()) ==> PathPoolMem(s.pathPool, s.pathPoolRaw)
// @ ensures   (err == nil && s.pathPoolInitialized())  ==> (
// @ 	PathPoolMemExceptOne(s.pathPool, s.pathPoolRaw, pathType) &&
// @    res === s.getPathPure(pathType))
// @ ensures   err != nil ==> (PathPoolMem(s.pathPool, s.pathPoolRaw) && err.ErrorMem())
// @ decreases
func (s *SCION) getPath(pathType path.Type) (res path.Path, err error) {
	// @ unfold PathPoolMem(s.pathPool, s.pathPoolRaw)
	if s.pathPool == nil {
		// @ ghost defer fold PathPoolMem(s.pathPool, s.pathPoolRaw)
		// @ EstablishPathPkgMem()
		return path.NewPath(pathType)
	}
	if int(pathType) < len(s.pathPool) {
		tmp := s.pathPool[pathType]
		// @ ghost if 0 < pathType {
		// @ 	fold   PathPoolMemExceptOne(s.pathPool, s.pathPoolRaw, pathType)
		// @ 	assert tmp.NonInitMem()
		// @ } else {
		// @ 	fold PathPoolMemExceptOne(s.pathPool, s.pathPoolRaw, pathType)
		// @ 	fold tmp.NonInitMem()
		// @ }
		return tmp, nil
	}
	tmp := s.pathPoolRaw
	// @ fold   PathPoolMemExceptOne(s.pathPool, s.pathPoolRaw, pathType)
	// @ assert tmp.NonInitMem()
	return tmp, nil
}

// @ requires  pb != nil
// @ requires  sl.Bytes(data, 0, len(data))
// @ preserves pb.Mem()
// @ ensures   res != nil ==> res.ErrorMem()
// @ decreases
func decodeSCION(data []byte, pb gopacket.PacketBuilder) (res error) {
	scn := &SCION{}
	// @ fold PathPoolMem(scn.pathPool, scn.pathPoolRaw)
	// @ fold scn.NonInitMem()
	err := scn.DecodeFromBytes(data, pb)
	if err != nil {
		return err
	}
	pb.AddLayer(scn)
	pb.SetNetworkLayer(scn)
	nextTmp := scionNextLayerType( /*@ unfolding scn.Mem(data) in @*/ scn.NextHdr)
	// @ fold nextTmp.Mem()
	return pb.NextDecoder(nextTmp)
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

// DstAddr parses the destination address into a addr.Host.
func (s *SCION) DstAddr() (addr.Host, error) {
	return ParseAddr(s.DstAddrType, s.RawDstAddr)
}

// SrcAddr parses the source address into a addr.Host.
func (s *SCION) SrcAddr() (addr.Host, error) {
	return ParseAddr(s.SrcAddrType, s.RawSrcAddr)
}

// SetDstAddr sets the destination address and updates the DstAddrType field accordingly.
func (s *SCION) SetDstAddr(dst addr.Host) error {
	var err error
	s.DstAddrType, s.RawDstAddr, err = PackAddr(dst)
	return err
}

// SetSrcAddr sets the source address and updates the DstAddrType field accordingly.
func (s *SCION) SetSrcAddr(src addr.Host) error {
	var err error
	s.SrcAddrType, s.RawSrcAddr, err = PackAddr(src)
	return err
}

func ParseAddr(addrType AddrType, raw []byte) (addr.Host, error) {
	switch addrType {
	case T4Ip:
		var raw4 [4]byte
		copy(raw4[:], raw)
		return addr.HostIP(netip.AddrFrom4(raw4)), nil
	case T4Svc:
		svc := addr.SVC(binary.BigEndian.Uint16(raw[:2]))
		return addr.HostSVC(svc), nil
	case T16Ip:
		var raw16 [16]byte
		copy(raw16[:], raw)
		return addr.HostIP(netip.AddrFrom16(raw16)), nil
	}
	return addr.Host{}, serrors.New("unsupported address type/length combination",
		"type", addrType, "len", addrType.Length())
}

func PackAddr(host addr.Host) (AddrType, []byte, error) {
	switch host.Type() {
	case addr.HostTypeIP:
		// The IP is potentially IPv4-in-IPv6. We need to unmap it to ensure
		// we only have true IPv4 or IPv6 addresses.
		ip := host.IP().Unmap()
		if !ip.IsValid() {
			break
		}
		if ip.Is6() {
			return T16Ip, ip.AsSlice(), nil
		}
		return T4Ip, ip.AsSlice(), nil
	case addr.HostTypeSVC:
		raw := make([]byte, 4)
		binary.BigEndian.PutUint16(raw, uint16(host.SVC()))
		return T4Svc, raw, nil
	}
	return 0, nil, serrors.New("unsupported address", "addr", host)
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
// @ preserves insideSlayers  ==> acc(&s.DstAddrType, R50) && acc(&s.SrcAddrType, R50)
// @ preserves insideSlayers  ==> (s.DstAddrType.Has3Bits() && s.SrcAddrType.Has3Bits())
// @ preserves !insideSlayers ==> acc(s.Mem(ubuf), R50)
// @ ensures   insideSlayers  ==> res == s.AddrHdrLenSpecInternal()
// @ ensures   !insideSlayers ==> res == s.AddrHdrLenSpec(ubuf)
// @ ensures   0 <= res
// @ decreases
func (s *SCION) AddrHdrLen( /*@ ghost ubuf []byte, ghost insideSlayers bool @*/ ) (res int) {
	// @ ghost if !insideSlayers {
	// @ 	unfold acc(s.Mem(ubuf), R51)
	// @ 	defer fold acc(s.Mem(ubuf), R51)
	// @ 	unfold acc(s.HeaderMem(ubuf[CmnHdrLen:]), R51)
	// @ 	defer fold acc(s.HeaderMem(ubuf[CmnHdrLen:]), R51)
	// @ 	assert s.AddrHdrLenSpec(ubuf) == (
	// @ 		unfolding acc(s.Mem(ubuf), R52) in
	// @ 		unfolding acc(s.HeaderMem(ubuf[CmnHdrLen:]), R52) in
	// @ 		2*addr.IABytes + s.DstAddrType.Length() + s.SrcAddrType.Length())
	// @ 	assert s.AddrHdrLenSpec(ubuf) ==
	// @ 		2*addr.IABytes + s.DstAddrType.Length() + s.SrcAddrType.Length()
	// @ }
	return 2*addr.IABytes + s.DstAddrType.Length() + s.SrcAddrType.Length()
}

// SerializeAddrHdr serializes destination and source ISD-AS-Host address triples into the provided
// buffer. The caller must ensure that the correct address types and lengths are set in the SCION
// layer, otherwise the results of this method are undefined.
// @ preserves acc(s.HeaderMem(ubuf), R10)
// @ preserves sl.Bytes(buf, 0, len(buf))
// @ preserves acc(sl.Bytes(ubuf, 0, len(ubuf)), R10)
// @ ensures   err != nil ==> err.ErrorMem()
// @ decreases
func (s *SCION) SerializeAddrHdr(buf []byte /*@ , ghost ubuf []byte @*/) (err error) {
	// @ unfold acc(s.HeaderMem(ubuf), R10)
	// @ defer fold acc(s.HeaderMem(ubuf), R10)
	if len(buf) < s.AddrHdrLen( /*@ nil, true @*/ ) {
		return serrors.New("provided buffer is too small", "expected", s.AddrHdrLen( /*@ nil, true @*/ ),
			"actual", len(buf))
	}
	dstAddrBytes := s.DstAddrType.Length()
	srcAddrBytes := s.SrcAddrType.Length()
	offset := 0
	// @ sl.SplitRange_Bytes(buf, offset, len(buf), writePerm)
	// @ unfold sl.Bytes(buf[offset:], 0, len(buf[offset:]))
	binary.BigEndian.PutUint64(buf[offset:], uint64(s.DstIA))
	// @ fold sl.Bytes(buf[offset:], 0, len(buf[offset:]))
	// @ sl.CombineRange_Bytes(buf, offset, len(buf), writePerm)
	offset += addr.IABytes
	// @ sl.SplitRange_Bytes(buf, offset, len(buf), writePerm)
	// @ unfold sl.Bytes(buf[offset:], 0, len(buf[offset:]))
	binary.BigEndian.PutUint64(buf[offset:], uint64(s.SrcIA))
	// @ fold sl.Bytes(buf[offset:], 0, len(buf[offset:]))
	// @ sl.CombineRange_Bytes(buf, offset, len(buf), writePerm)
	offset += addr.IABytes
	// @ sl.SplitRange_Bytes(buf, offset, offset+dstAddrBytes, writePerm)
	// @ sl.SplitRange_Bytes(ubuf, offset, offset+dstAddrBytes, R10)

	// @ unfold sl.Bytes(buf[offset:offset+dstAddrBytes], 0, len(buf[offset:offset+dstAddrBytes]))
	// @ unfold acc(sl.Bytes(ubuf[offset:offset+dstAddrBytes], 0, len(ubuf[offset:offset+dstAddrBytes])), R10)
	copy(buf[offset:offset+dstAddrBytes], s.RawDstAddr /*@ , R10 @*/)
	// @ fold sl.Bytes(buf[offset:offset+dstAddrBytes], 0, len(buf[offset:offset+dstAddrBytes]))
	// @ fold acc(sl.Bytes(ubuf[offset:offset+dstAddrBytes], 0, len(ubuf[offset:offset+dstAddrBytes])), R10)
	// @ sl.CombineRange_Bytes(buf, offset, offset+dstAddrBytes, writePerm)
	// @ sl.CombineRange_Bytes(ubuf, offset, offset+dstAddrBytes, R10)

	offset += dstAddrBytes
	// @ sl.SplitRange_Bytes(buf, offset, offset+srcAddrBytes, writePerm)
	// @ sl.SplitRange_Bytes(ubuf, offset, offset+srcAddrBytes, R10)

	// @ unfold sl.Bytes(buf[offset:offset+srcAddrBytes], 0, len(buf[offset:offset+srcAddrBytes]))
	// @ unfold acc(sl.Bytes(ubuf[offset:offset+srcAddrBytes], 0, len(ubuf[offset:offset+srcAddrBytes])), R10)

	copy(buf[offset:offset+srcAddrBytes], s.RawSrcAddr /*@ , R10 @*/)

	// @ fold sl.Bytes(buf[offset:offset+srcAddrBytes], 0, len(buf[offset:offset+srcAddrBytes]))
	// @ fold acc(sl.Bytes(ubuf[offset:offset+srcAddrBytes], 0, len(ubuf[offset:offset+srcAddrBytes])), R10)
	// @ sl.CombineRange_Bytes(buf, offset, offset+srcAddrBytes, writePerm)
	// @ sl.CombineRange_Bytes(ubuf, offset, offset+srcAddrBytes, R10)

	return nil
}

// DecodeAddrHdr decodes the destination and source ISD-AS-Host address triples from the provided
// buffer. The caller must ensure that the correct address types and lengths are set in the SCION
// layer, otherwise the results of this method are undefined.
// @ requires  acc(&s.SrcIA) && acc(&s.DstIA)
// @ requires  acc(&s.SrcAddrType, HalfPerm) && s.SrcAddrType.Has3Bits()
// @ requires  acc(&s.DstAddrType, HalfPerm) && s.DstAddrType.Has3Bits()
// @ requires  acc(&s.RawSrcAddr) && acc(&s.RawDstAddr)
// @ preserves acc(sl.Bytes(data, 0, len(data)), R41)
// @ ensures   res == nil ==> s.HeaderMem(data)
// @ ensures   res != nil ==> res.ErrorMem()
// @ ensures   res != nil ==> (
// @	acc(&s.SrcIA) && acc(&s.DstIA) &&
// @ 	acc(&s.SrcAddrType, HalfPerm) && acc(&s.DstAddrType, HalfPerm) &&
// @ 	acc(&s.RawSrcAddr) && acc(&s.RawDstAddr))
// @ decreases
func (s *SCION) DecodeAddrHdr(data []byte) (res error) {
	// @ ghost l := s.AddrHdrLenSpecInternal()
	if len(data) < s.AddrHdrLen( /*@ nil, true @*/ ) {
		return serrors.New("provided buffer is too small", "expected", s.AddrHdrLen( /*@ nil, true @*/ ),
			"actual", len(data))
	}
	offset := 0
	// @ unfold acc(sl.Bytes(data, 0, len(data)), R41)
	// @ assert forall i int :: { &data[offset:][i] }{ &data[i] } 0 <= i && i < l ==> &data[offset:][i] == &data[i]
	s.DstIA = addr.IA(binary.BigEndian.Uint64(data[offset:]))
	offset += addr.IABytes
	// @ assert forall i int :: { &data[offset:][i] } 0 <= i && i < l ==> &data[offset:][i] == &data[offset+i]
	s.SrcIA = addr.IA(binary.BigEndian.Uint64(data[offset:]))
	// @ fold acc(sl.Bytes(data, 0, len(data)), R41)
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
// @ requires  acc(&s.RawSrcAddr, R20) && acc(&s.RawDstAddr, R20)
// @ requires  len(s.RawSrcAddr) % 2 == 0 && len(s.RawDstAddr) % 2 == 0
// @ requires  acc(&s.SrcIA, R20) && acc(&s.DstIA, R20)
// @ requires  acc(sl.Bytes(s.RawSrcAddr, 0, len(s.RawSrcAddr)), R20)
// @ requires  acc(sl.Bytes(s.RawDstAddr, 0, len(s.RawDstAddr)), R20)
// @ preserves acc(sl.Bytes(upperLayer, 0, len(upperLayer)), R20)
// @ ensures   acc(&s.RawSrcAddr, R20) && acc(&s.RawDstAddr, R20)
// @ ensures   acc(&s.SrcIA, R20) && acc(&s.DstIA, R20)
// @ ensures   acc(sl.Bytes(s.RawSrcAddr, 0, len(s.RawSrcAddr)), R20)
// @ ensures   acc(sl.Bytes(s.RawDstAddr, 0, len(s.RawDstAddr)), R20)
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

// @ requires acc(&s.RawSrcAddr, R20) && acc(&s.RawDstAddr, R20)
// @ requires len(s.RawSrcAddr) % 2 == 0 && len(s.RawDstAddr) % 2 == 0
// @ requires acc(&s.SrcIA, R20) && acc(&s.DstIA, R20)
// @ requires acc(sl.Bytes(s.RawSrcAddr, 0, len(s.RawSrcAddr)), R20)
// @ requires acc(sl.Bytes(s.RawDstAddr, 0, len(s.RawDstAddr)), R20)
// @ ensures  acc(&s.RawSrcAddr, R20) && acc(&s.RawDstAddr, R20)
// @ ensures  acc(&s.SrcIA, R20) && acc(&s.DstIA, R20)
// @ ensures  acc(sl.Bytes(s.RawSrcAddr, 0, len(s.RawSrcAddr)), R20)
// @ ensures  acc(sl.Bytes(s.RawDstAddr, 0, len(s.RawDstAddr)), R20)
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
	// @ invariant acc(&s.RawSrcAddr, R20) && acc(sl.Bytes(s.RawSrcAddr, 0, len(s.RawSrcAddr)), R20)
	// @ invariant len(s.RawSrcAddr) == rawSrcAddrLen
	// @ invariant len(s.RawSrcAddr) % 2 == 0
	// @ invariant i % 2 == 0
	// @ invariant 0 <= i && i <= len(s.RawSrcAddr)
	// @ decreases len(s.RawSrcAddr) - i
	for i := 0; i < len(s.RawSrcAddr); i += 2 {
		// @ preserves err == nil
		// @ requires acc(&s.RawSrcAddr, R20) && acc(sl.Bytes(s.RawSrcAddr, 0, len(s.RawSrcAddr)), R20)
		// @ requires 0 <= i && i < len(s.RawSrcAddr) && i % 2 == 0 && len(s.RawSrcAddr) % 2 == 0
		// @ ensures acc(&s.RawSrcAddr, R20) && acc(sl.Bytes(s.RawSrcAddr, 0, len(s.RawSrcAddr)), R20)
		// @ ensures s.RawSrcAddr === before(s.RawSrcAddr)
		// @ decreases
		// @ outline(
		// @ unfold acc(sl.Bytes(s.RawSrcAddr, 0, len(s.RawSrcAddr)), R20)
		csum += uint32(s.RawSrcAddr[i]) << 8
		csum += uint32(s.RawSrcAddr[i+1])
		// @ fold acc(sl.Bytes(s.RawSrcAddr, 0, len(s.RawSrcAddr)), R20)
		// @ )
	}
	// @ ghost var rawDstAddrLen int = len(s.RawDstAddr)
	// @ invariant acc(&s.RawDstAddr, R20) && acc(sl.Bytes(s.RawDstAddr, 0, len(s.RawDstAddr)), R20)
	// @ invariant len(s.RawDstAddr) == rawDstAddrLen
	// @ invariant len(s.RawDstAddr) % 2 == 0
	// @ invariant i % 2 == 0
	// @ invariant 0 <= i && i <= len(s.RawDstAddr)
	// @ decreases len(s.RawDstAddr) - i
	for i := 0; i < len(s.RawDstAddr); i += 2 {
		// @ preserves err == nil
		// @ requires acc(&s.RawDstAddr, R20) && acc(sl.Bytes(s.RawDstAddr, 0, len(s.RawDstAddr)), R20)
		// @ requires 0 <= i && i < len(s.RawDstAddr) && i % 2 == 0 && len(s.RawDstAddr) % 2 == 0
		// @ ensures acc(&s.RawDstAddr, R20) && acc(sl.Bytes(s.RawDstAddr, 0, len(s.RawDstAddr)), R20)
		// @ ensures s.RawDstAddr === before(s.RawDstAddr)
		// @ decreases
		// @ outline(
		// @ unfold acc(sl.Bytes(s.RawDstAddr, 0, len(s.RawDstAddr)), R20)
		csum += uint32(s.RawDstAddr[i]) << 8
		csum += uint32(s.RawDstAddr[i+1])
		// @ fold acc(sl.Bytes(s.RawDstAddr, 0, len(s.RawDstAddr)), R20)
		// @ )
	}
	l := uint32(length)
	csum += (l >> 16) + (l & 0xffff)
	csum += uint32(protocol)
	return csum, nil
}

// @ preserves acc(sl.Bytes(upperLayer, 0, len(upperLayer)), R20)
// @ decreases
func (s *SCION) upperLayerChecksum(upperLayer []byte, csum uint32) uint32 {
	// Compute safe boundary to ensure we do not access out of bounds.
	// Odd lengths are handled at the end.
	safeBoundary := len(upperLayer) - 1
	// @ unfold acc(sl.Bytes(upperLayer, 0, len(upperLayer)), R20)
	// @ invariant 0 <= i && i < safeBoundary + 2
	// @ invariant i % 2 == 0
	// @ invariant forall i int :: { &upperLayer[i] } 0 <= i && i < len(upperLayer) ==> acc(&upperLayer[i], R20)
	// @ decreases safeBoundary - i
	for i := 0; i < safeBoundary; i += 2 {
		csum += uint32(upperLayer[i]) << 8
		csum += uint32(upperLayer[i+1])
	}
	if len(upperLayer)%2 == 1 {
		csum += uint32(upperLayer[safeBoundary]) << 8
	}
	// @ fold acc(sl.Bytes(upperLayer, 0, len(upperLayer)), R20)
	return csum
}

// (VerifiedSCION) The following function terminates but Gobra can't
// deduce that because of limited support of bitwise operations.
// @ decreases
func (s *SCION) foldChecksum(csum uint32) (res uint16) {
	// @ decreases csum
	for csum > 0xffff {
		// @ b.FoldChecksumLemma(csum)
		csum = (csum >> 16) + (csum & 0xffff)
	}
	return ^uint16(csum)
}
