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

//@ initEnsures path.PathPackageMem()
//@ initEnsures path.Registered(empty.PathType)
//@ initEnsures path.Registered(epic.PathType)
//@ initEnsures path.Registered(onehop.PathType)
//@ initEnsures path.Registered(scion.PathType)
package slayers

import (
	"encoding/binary"
	"net"

	"github.com/google/gopacket"

	"github.com/scionproto/scion/pkg/addr"
	"github.com/scionproto/scion/pkg/private/serrors"
	//@ importRequires path.PathPackageMem()
	"github.com/scionproto/scion/pkg/slayers/path"
	"github.com/scionproto/scion/pkg/slayers/path/empty"
	"github.com/scionproto/scion/pkg/slayers/path/epic"
	"github.com/scionproto/scion/pkg/slayers/path/onehop"
	"github.com/scionproto/scion/pkg/slayers/path/scion"
	//@ "github.com/scionproto/scion/verification/utils/definitions"
	//@ "github.com/scionproto/scion/verification/utils/slices"
)

const (
	// LineLen is the length of a SCION header line in bytes.
	LineLen = 4
	// CmnHdrLen is the length of the SCION common header in bytes.
	CmnHdrLen = 12
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

// AddrLen indicates the length of a host address in the SCION header. The four possible lengths are
// 4, 8, 12, or 16 bytes.
type AddrLen uint8

// AddrLen constants
const (
	AddrLen4 AddrLen = iota
	AddrLen8
	AddrLen12
	AddrLen16
)

// AddrType indicates the type of a host address of a given length in the SCION header. There are
// four possible types per address length.
type AddrType uint8

// AddrType constants
const (
	T4Ip AddrType = iota
	T4Svc
)

// AddrLen16 types
const (
	T16Ip AddrType = iota
)

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
//@ requires b.LayerMem()
//@ ensures  slices.AbsSlice_Bytes(res, 0, len(res))
//@ ensures  slices.AbsSlice_Bytes(res, 0, len(res)) --* b.LayerMem()
func (b *BaseLayer) LayerContents() (res []byte) {
	//@ unfold b.LayerMem()
	//@ unfold slices.AbsSlice_Bytes(b.Contents, 0, len(b.Contents))
	res = b.Contents
	//@ fold slices.AbsSlice_Bytes(res, 0, len(res))
	//@ package slices.AbsSlice_Bytes(res, 0, len(res)) --* b.LayerMem() {
	//@   fold b.LayerMem()
	//@ }
	return res
}

// LayerPayload returns the bytes contained within the packet layer.
//@ requires b.PayloadMem()
//@ ensures slices.AbsSlice_Bytes(res, 0, len(res))
//@ ensures slices.AbsSlice_Bytes(res, 0, len(res)) --* b.PayloadMem()
func (b *BaseLayer) LayerPayload() (res []byte) {
	//@ unfold b.PayloadMem()
	//@ unfold slices.AbsSlice_Bytes(b.Payload, 0, len(b.Payload))
	res = b.Payload
	//@ fold slices.AbsSlice_Bytes(res, 0, len(res))
	//@ package slices.AbsSlice_Bytes(res, 0, len(res)) --* b.PayloadMem() {
	//@   fold b.PayloadMem()
	//@ }
	return res
}

// SCION is the header of a SCION packet.
type SCION struct {
	BaseLayer
	// Common Header fields

	// TODO (gavinleroy) ghost fields for the SCION struct.
	// Gobra currently has no support for ghost fields, however,
	// this information is required to ensure safe memory transfer
	// during reuse and well-formedness. The following should not
	// be referred to outside of ghost positions.
	//@ pathMemLoc PathMemLoc
	//@ hdrBytes int

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
	// maximum of 1024 bytes.
	HdrLen uint8
	// PayloadLen is the length of the payload in bytes. The payload includes extension headers and
	// the L4 payload. This field is 16 bits long, supporting a maximum payload size of 64KB.
	PayloadLen uint16
	// PathType specifies the type of path in this SCION header.
	PathType path.Type
	// DstAddrType (2 bit) is the type of the destination address.
	DstAddrType AddrType
	// DstAddrLen (2 bit) is the length of the destination address. Supported address length are 4B
	// (0), 8B (1), 12B (2), and 16B (3).
	DstAddrLen AddrLen
	// SrcAddrType (2 bit) is the type of the source address.
	SrcAddrType AddrType
	// SrcAddrLen (2 bit) is the length of the source address. Supported address length are 4B (0),
	// 8B (1), 12B (2), and 16B (3).
	SrcAddrLen AddrLen

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

//@ pure
//@ requires acc(s.Mem(), _)
//@ decreases
func (s *SCION) LayerType() gopacket.LayerType {
	// TODO once the globals PR is merged uncomment the original statement
	// return LayerTypeSCION
	return getLayerTypeSCION()
}

//@ preserves s.Mem()
//@ ensures   res.Mem()
//@ decreases
func (s *SCION) CanDecode() (res gopacket.LayerClass) {
	// TODO once the globals PR is merged uncomment the original statement
	// return LayerClassSCION
	return getLayerClassSCION()
}

//@ preserves s.Mem()
//@ decreases
func (s *SCION) NextLayerType() gopacket.LayerType {
	return scionNextLayerType(s.NextHdr)
}

// TODO in the previous code this method only returned /read/
// access to the payload, do we still want that or is write access
// desireable?
//@ requires s.Mem()
//@ ensures slices.AbsSlice_Bytes(res, 0, len(res))
//@ ensures slices.AbsSlice_Bytes(res, 0, len(res)) --* s.Mem()
//@ decreases
func (s *SCION) LayerPayload() (res []byte) {
	//@ unfold s.Mem()
	//@ unfold s.BaseLayer.Mem()
	res = s.Payload
	//@ package slices.AbsSlice_Bytes(res, 0, len(res)) --* s.Mem() {
	//@   fold s.BaseLayer.Mem()
	//@   fold s.Mem()
	//@ }
	return res
}

//@ requires false
//@ decreases
func (s *SCION) NetworkFlow() gopacket.Flow {
	// TODO(shitz): Investigate how we can use gopacket.Flow.
	return gopacket.Flow{}
}

//@ requires  s != nil
//@ requires  b != nil
//@ requires  b.Mem(buf_init)
//@ preserves s.Mem()
//@ ensures   err == nil ==> buf_res != nil
//@ ensures   err == nil ==> b.Mem(buf_res)
// ensures   err != nil ==> b.Mem(buf_init)
//@ ensures   err != nil ==> err.ErrorMem()
//@ decreases
func (s *SCION) SerializeTo(b gopacket.SerializeBuffer, opts gopacket.SerializeOptions /*@ , ghost buf_init []byte @*/) (err error /*@, ghost buf_res []byte @*/) {
	scnLen := CmnHdrLen + /*@ unfolding s.Mem() in @*/ s.AddrHdrLen() + s.Path.Len()
	//@ assert scnLen >= 0
	buf, err /*@, buf_res @*/ := b.PrependBytes(scnLen /*@ , buf_init @*/)
	if err != nil {
		return err /*@, nil @*/
	}
	if opts.FixLengths {
		//@ unfold s.Mem()
		s.HdrLen = uint8(scnLen / LineLen)
		buf_tmp := b.Bytes( /*@ buf_res @*/ )
		//@ assert len(buf_tmp) == len(buf_res)
		s.PayloadLen = uint16(len(buf_tmp) - scnLen)
		//@ apply slices.AbsSlice_Bytes(buf_res, 0, len(buf_res)) --* b.Mem(buf_res)
		//@ fold s.Mem()
	}
	//@ assert b.Mem(buf_res)
	//@ assert b.Mem(buf_res)
	//@ ghost b.ExchangePred(buf_res)
	//@ assert slices.AbsSlice_Bytes(buf_res, 0, len(buf_res))
	//@ ghost slices.SplitByIndex_Bytes(buf_res, 0, len(buf_res), scnLen, writePerm)
	//@ requires slices.AbsSlice_Bytes(buf_res, 0, scnLen)
	//@ requires slices.AbsSlice_Bytes(buf_res, scnLen, len(buf_res))
	//@ ensures slices.AbsSlice_Bytes(buf, 0, len(buf))
	//@ ensures slices.AbsSlice_Bytes(buf_res, scnLen, len(buf_res))
	//@ decreases
	//@ outline(
	//@ ghost slices.Reslice_Bytes(buf_res, 0, scnLen, writePerm)
	//@ assert slices.AbsSlice_Bytes(buf, 0, len(buf))
	//@ assert len(buf) >= unfolding acc(s.Mem(), _) in CmnHdrLen + s.AddrHdrLen() + s.Path.Len()
	//@ ghost len_buf := unfolding acc(s.Mem(), _) in CmnHdrLen + s.AddrHdrLen() + s.Path.Len()
	//@ assert len_buf == unfolding acc(s.Mem(), _) in CmnHdrLen + s.AddrHdrLen() + s.Path.Len()
	//@ )
	//@ preserves acc(s.Mem(), definitions.ReadL1)
	//@ decreases
	//@ outline (
	//@ unfold acc(s.Mem(), definitions.ReadL1)
	// Serialize common header.
	firstLine := uint32(s.Version&0xF)<<28 | uint32(s.TrafficClass)<<20 | s.FlowID&0xFFFFF
	//@ fold acc(s.Mem(), definitions.ReadL1)
	//@ )
	//@ requires  acc(s.Mem(), definitions.ReadL1)
	//@ requires  len(buf) >= unfolding acc(s.Mem(), _) in CmnHdrLen + s.AddrHdrLen() + s.Path.Len()
	//@ requires  slices.AbsSlice_Bytes(buf, 0, len(buf))
	//@ ensures   acc(s.Mem(), definitions.ReadL1)
	//@ ensures   slices.AbsSlice_Bytes(buf, 0, 6)
	//@ ensures   slices.AbsSlice_Bytes(buf, 6, len(buf))
	//@ decreases
	//@ outline(
	//@ unfold acc(s.Mem(), definitions.ReadL2)
	//@ ghost slices.SplitByIndex_Bytes(buf, 0, len(buf), 4, writePerm)
	//@ ghost slices.Reslice_Bytes(buf, 0, 4, writePerm)
	//@ unfold slices.AbsSlice_Bytes(buf[:4], 0, len(buf[:4]))
	binary.BigEndian.PutUint32(buf[:4], firstLine)
	//@ fold slices.AbsSlice_Bytes(buf[:4], 0, len(buf[:4]))
	//@ ghost slices.Unslice_Bytes(buf, 0, 4, writePerm)
	//@ ghost slices.SplitByIndex_Bytes(buf, 4, len(buf), 6, writePerm)
	//@ unfold slices.AbsSlice_Bytes(buf, 4, 6)
	buf[4] = uint8(s.NextHdr)
	buf[5] = s.HdrLen
	//@ fold slices.AbsSlice_Bytes(buf, 4, 6)
	//@ ghost slices.CombineAtIndex_Bytes(buf, 0, 6, 4, writePerm)
	//@ fold acc(s.Mem(), definitions.ReadL2)
	//@ )
	//@ requires  acc(s.Mem(), definitions.ReadL1)
	//@ requires  len(buf) >= unfolding acc(s.Mem(), _) in CmnHdrLen + s.AddrHdrLen() + s.Path.Len()
	//@ requires  slices.AbsSlice_Bytes(buf, 0, 6)
	//@ requires  slices.AbsSlice_Bytes(buf, 6, len(buf))
	//@ ensures   acc(s.Mem(), definitions.ReadL1)
	//@ ensures   slices.AbsSlice_Bytes(buf, 0, 10)
	//@ ensures   slices.AbsSlice_Bytes(buf, 10, len(buf))
	//@ ensures   len(buf) == before(len(buf))
	//@ decreases
	//@ outline(
	//@ unfold acc(s.Mem(), definitions.ReadL2)
	//@ ghost slices.SplitByIndex_Bytes(buf, 6, len(buf), 8, writePerm)
	//@ ghost slices.Reslice_Bytes(buf, 6, 8, writePerm)
	//@ unfold slices.AbsSlice_Bytes(buf[6:8], 0, len(buf[6:8]))
	binary.BigEndian.PutUint16(buf[6:8], s.PayloadLen)
	//@ fold slices.AbsSlice_Bytes(buf[6:8], 0, len(buf[6:8]))
	//@ ghost slices.Unslice_Bytes(buf, 6, 8, writePerm)
	//@ ghost slices.CombineAtIndex_Bytes(buf, 0, 8, 6, writePerm)
	//@ ghost slices.SplitByIndex_Bytes(buf, 8, len(buf), 10, writePerm)
	//@ unfold slices.AbsSlice_Bytes(buf, 8, 10)
	buf[8] = uint8(s.PathType)
	buf[9] = uint8(s.DstAddrType&0x3)<<6 | uint8(s.DstAddrLen&0x3)<<4 |
		uint8(s.SrcAddrType&0x3)<<2 | uint8(s.SrcAddrLen&0x3)
	//@ fold slices.AbsSlice_Bytes(buf, 8, 10)
	//@ ghost slices.CombineAtIndex_Bytes(buf, 0, 10, 8, writePerm)
	//@ fold acc(s.Mem(), definitions.ReadL2)
	//@ )
	//@ requires slices.AbsSlice_Bytes(buf, 0, 10)
	//@ requires slices.AbsSlice_Bytes(buf, 10, len(buf))
	//@ ensures  slices.AbsSlice_Bytes(buf, 0, CmnHdrLen)
	//@ ensures  slices.AbsSlice_Bytes(buf, CmnHdrLen, len(buf))
	//@ ensures  len(buf) == before(len(buf))
	//@ decreases
	//@ outline(
	//@ ghost slices.SplitByIndex_Bytes(buf, 10, len(buf), 12, writePerm)
	//@ ghost slices.Reslice_Bytes(buf, 10, 12, writePerm)
	//@ unfold slices.AbsSlice_Bytes(buf[10:12], 0, len(buf[10:12]))
	binary.BigEndian.PutUint16(buf[10:12], 0)
	//@ fold slices.AbsSlice_Bytes(buf[10:12], 0, len(buf[10:12]))
	//@ ghost slices.Unslice_Bytes(buf, 10, 12, writePerm)
	//@ ghost slices.CombineAtIndex_Bytes(buf, 0, 12, 10, writePerm)
	//@ )
	//@ requires  acc(s.Mem(), definitions.ReadL1)
	//@ requires  len(buf) >= unfolding acc(s.Mem(), _) in CmnHdrLen + s.AddrHdrLen() + s.Path.Len()
	//@ preserves slices.AbsSlice_Bytes(buf, 0, CmnHdrLen)
	//@ preserves slices.AbsSlice_Bytes(buf, CmnHdrLen, len(buf))
	//@ ensures   acc(s.Mem(), definitions.ReadL1)
	//@ ensures   len(buf) == before(len(buf))
	//@ ensures   tmp != nil ==> tmp.ErrorMem()
	//@ decreases
	//@ outline(
	//@ unfold acc(s.Mem(), definitions.ReadL1)
	//@ fold acc(s.AddrHdrMem(), definitions.ReadL2)
	//@ ghost slices.Reslice_Bytes(buf, CmnHdrLen, len(buf), writePerm)
	tmp := s.SerializeAddrHdr(buf[CmnHdrLen:])
	//@ ghost slices.Unslice_Bytes(buf, CmnHdrLen, len(buf), writePerm)
	//@ unfold acc(s.AddrHdrMem(), definitions.ReadL2)
	//@ fold acc(s.Mem(), definitions.ReadL1)
	//@ assert acc(s.Mem(), definitions.ReadL1)
	//@ )
	// Serialize address header.
	if err := tmp; err != nil {
		//@ ghost slices.CombineAtIndex_Bytes(buf, 0, len(buf), CmnHdrLen, writePerm)
		//@ assert len(buf) == scnLen
		//@ assert slices.AbsSlice_Bytes(buf, 0, len(buf))
		//@ assert slices.AbsSlice_Bytes(buf_res[0:scnLen], 0, len(buf_res[0:scnLen]))
		//@ ghost slices.Unslice_Bytes(buf_res, 0, scnLen, writePerm)
		//@ ghost slices.CombineAtIndex_Bytes(buf_res, 0, len(buf_res), scnLen, writePerm)
		//@ apply slices.AbsSlice_Bytes(buf_res, 0, len(buf_res)) --* b.Mem(buf_res)
		return err /*@, nil @*/
	}
	//@ requires  s.Mem()
	//@ requires  len(buf) >= unfolding acc(s.Mem(), _) in CmnHdrLen + s.AddrHdrLen() + s.Path.Len()
	//@ requires  slices.AbsSlice_Bytes(buf, 0, CmnHdrLen)
	//@ requires  slices.AbsSlice_Bytes(buf, CmnHdrLen, len(buf))
	//@ ensures   s.Mem()
	//@ ensures   slices.AbsSlice_Bytes(buf, 0, len(buf))
	//@ ensures   len(buf) == before(len(buf))
	//@ ensures   res != nil ==> res.ErrorMem()
	//@ decreases
	//@ outline(
	//@ unfold s.Mem()
	offset := CmnHdrLen + s.AddrHdrLen()
	//@ assert offset >= CmnHdrLen && offset <= len(buf)
	//@ ghost slices.SplitByIndex_Bytes(buf, CmnHdrLen, len(buf), offset, writePerm)
	//@ ghost slices.CombineAtIndex_Bytes(buf, 0, offset, CmnHdrLen, writePerm)
	//@ ghost slices.Reslice_Bytes(buf, offset, len(buf), writePerm)
	// Serialize path header.
	res := s.Path.SerializeTo(buf[offset:])
	//@ ghost slices.Unslice_Bytes(buf, offset, len(buf), writePerm)
	//@ ghost slices.CombineAtIndex_Bytes(buf, 0, len(buf), offset, writePerm)
	//@ fold s.Mem()
	//@ )
	//@ ghost slices.Unslice_Bytes(buf_res, 0, scnLen, writePerm)
	//@ ghost slices.CombineAtIndex_Bytes(buf_res, 0, len(buf_res), scnLen, writePerm)
	//@ apply slices.AbsSlice_Bytes(buf_res, 0, len(buf_res)) --* b.Mem(buf_res)
	return res /*@, buf_res @*/
}

// DecodeFromBytes decodes the SCION layer. DecodeFromBytes resets the internal state of this layer
// to the state defined by the passed-in bytes. Slices in the SCION layer reference the passed-in
// data, so care should be taken to copy it first should later modification of data be required
// before the SCION layer is discarded.
//@ requires  slices.AbsSlice_Bytes(data, 0, len(data))
//@ requires  s.NonInitMem()
//@ requires  df != nil
//@ preserves acc(path.PathPackageMem(), definitions.ReadL20)
//@ preserves df.Mem()
//@ ensures   res == nil ==> s.Mem()
//@ ensures   res == nil ==> s.GetUnderlyingBuf() === data
//@ ensures   res != nil ==> s.NonInitMem()
//@ ensures   res != nil ==> res.ErrorMem()
//@ ensures   res != nil ==> slices.AbsSlice_Bytes(data, 0, len(data))
//@ decreases
func (s *SCION) DecodeFromBytes(data []byte, df gopacket.DecodeFeedback) (res error) {
	// Decode common header.
	if len(data) < CmnHdrLen {
		df.SetTruncated()
		return serrors.New("packet is shorter than the common header length",
			"min", int(CmnHdrLen), "actual", int(len(data)))
	}
	//@ ghost slices.SplitByIndex_Bytes(data, 0, len(data), 6, writePerm)
	//@ ghost slices.SplitByIndex_Bytes(data, 0, 6, 4, writePerm)
	//@ unfold s.NonInitMem()
	//@ preserves acc(slices.AbsSlice_Bytes(data, 0, 4), definitions.ReadL1)
	//@ ensures   firstLine >= 0
	//@ decreases
	//@ outline(
	//@ ghost slices.Reslice_Bytes(data, 0, 4, definitions.ReadL1)
	//@ unfold acc(slices.AbsSlice_Bytes(data[:4], 0, len(data[:4])), definitions.ReadL2)
	firstLine := binary.BigEndian.Uint32(data[:4])
	//@ fold acc(slices.AbsSlice_Bytes(data[:4], 0, len(data[:4])), definitions.ReadL2)
	//@ ghost slices.Unslice_Bytes(data, 0, 4, definitions.ReadL1)
	//@ )
	s.Version = uint8(firstLine >> 28)
	s.TrafficClass = uint8((firstLine >> 20) & 0xFF)
	s.FlowID = firstLine & 0xFFFFF
	// NOTE (gavinleroy) Gobra doesn't recognize a uint cast as
	// returning non-negative values.
	//@ assume s.Version >= 0
	//@ assume s.TrafficClass >= 0
	//@ preserves acc(slices.AbsSlice_Bytes(data, 4, 6), definitions.ReadL1)
	//@ preserves acc(&s.NextHdr)
	//@ preserves acc(&s.HdrLen)
	//@ ensures   s.HdrLen >= 0
	//@ decreases
	//@ outline(
	//@ unfold acc(slices.AbsSlice_Bytes(data, 4, 6), definitions.ReadL1)
	s.NextHdr = L4ProtocolType(data[4])
	s.HdrLen = data[5]
	//@ fold acc(slices.AbsSlice_Bytes(data, 4, 6), definitions.ReadL1)
	// NOTE s.HdrLen is an /unsigned integer/ but Gobra does not recognize
	// that is is always >= 0.
	//@ assume s.HdrLen >= 0
	//@ )
	//@ ghost slices.CombineAtIndex_Bytes(data, 0, 6, 4, writePerm)
	//@ ghost slices.SplitByIndex_Bytes(data, 6, len(data), 10, writePerm)
	//@ ghost slices.SplitByIndex_Bytes(data, 6, 10, 8, writePerm)
	//@ preserves acc(slices.AbsSlice_Bytes(data, 6, 8), definitions.ReadL1)
	//@ preserves acc(&s.PayloadLen)
	//@ ensures   s.PayloadLen >= 0
	//@ decreases
	//@ outline(
	//@ ghost slices.Reslice_Bytes(data, 6, 8, definitions.ReadL1)
	//@ unfold acc(slices.AbsSlice_Bytes(data[6:8], 0, 2), definitions.ReadL1)
	s.PayloadLen = binary.BigEndian.Uint16(data[6:8])
	//@ fold acc(slices.AbsSlice_Bytes(data[6:8], 0, 2), definitions.ReadL1)
	//@ ghost slices.Unslice_Bytes(data, 6, 8, definitions.ReadL1)
	//@ )
	//@ preserves acc(slices.AbsSlice_Bytes(data, 8, 10), definitions.ReadL1)
	//@ preserves acc(&s.PathType)
	//@ preserves acc(&s.DstAddrType)
	//@ preserves acc(&s.DstAddrLen)
	//@ preserves acc(&s.SrcAddrType)
	//@ preserves acc(&s.SrcAddrLen)
	//@ ensures   s.DstAddrLen >= 0
	//@ ensures   s.SrcAddrLen >= 0
	//@ ensures   0 <= s.PathType && s.PathType < path.maxPathType
	//@ decreases
	//@ outline(
	//@ unfold acc(slices.AbsSlice_Bytes(data, 8, 10), definitions.ReadL1)
	s.PathType = path.Type(data[8])
	s.DstAddrType = AddrType(data[9] >> 6)
	s.DstAddrLen = AddrLen(data[9] >> 4 & 0x3)
	s.SrcAddrType = AddrType(data[9] >> 2 & 0x3)
	s.SrcAddrLen = AddrLen(data[9] & 0x3)
	//@ fold acc(slices.AbsSlice_Bytes(data, 8, 10), definitions.ReadL1)
	// NOTE AddrLen & PathTYpe are aliases to uint, which Gobra doesn't
	// recognize. maxPathType is 256, the maximum number for uint8, thus
	// we also add this knowledge after reading the byte.
	//@ assume s.DstAddrLen >= 0
	//@ assume s.SrcAddrLen >= 0
	//@ assume s.PathType >= 0
	//@ assume s.PathType < path.maxPathType
	//@ )
	//@ ghost slices.CombineAtIndex_Bytes(data, 6, 10, 8, writePerm)
	//@ ghost slices.CombineAtIndex_Bytes(data, 0, 10, 6, writePerm)
	//@ ghost slices.CombineAtIndex_Bytes(data, 0, len(data), 10, writePerm)
	//@ ghost slices.SplitByIndex_Bytes(data, 0, len(data), CmnHdrLen, writePerm)
	//@ requires 0 <= CmnHdrLen && CmnHdrLen <= len(data)
	//@ requires slices.AbsSlice_Bytes(data, CmnHdrLen, len(data))
	//@ ensures slices.AbsSlice_Bytes(data[CmnHdrLen:], 0, len(data[CmnHdrLen:]))
	//@ decreases
	//@ outline(
	//@ ghost slices.Reslice_Bytes(data, CmnHdrLen, len(data), writePerm)
	//@ )
	//@ fold s.AddrHdrInitMem()
	tmp_err /*@, end_idx @*/ := s.DecodeAddrHdr(data[CmnHdrLen:])
	// Decode address header.
	if err := tmp_err; err != nil {
		df.SetTruncated()
		//@ ghost slices.Unslice_Bytes(data, CmnHdrLen, len(data), writePerm)
		//@ ghost slices.CombineAtIndex_Bytes(data, 0, len(data), CmnHdrLen, writePerm)
		//@ unfold s.AddrHdrInitMem()
		//@ fold s.NonInitMem()
		//@ assert err.ErrorMem()
		return err
	}
	//@ assert data[CmnHdrLen:][end_idx:] === data[(CmnHdrLen + end_idx):]
	//@ assert slices.AbsSlice_Bytes(data[CmnHdrLen:][end_idx:], 0, len(data[CmnHdrLen:][end_idx:]))
	//@ assert slices.AbsSlice_Bytes(data[CmnHdrLen + end_idx:], 0, len(data[CmnHdrLen + end_idx:]))
	//@ ghost slices.Unslice_Bytes(data, CmnHdrLen + end_idx, len(data), writePerm)
	//@ assert slices.AbsSlice_Bytes(data, CmnHdrLen + end_idx, len(data))
	//@ assert s.AddrHdrMem()
	//@ assert end_idx == unfolding s.AddrHdrMem() in s.AddrHdrLen()
	addrHdrLen := /*@ unfolding s.AddrHdrMem() in @*/ s.AddrHdrLen()
	//@ assert end_idx == addrHdrLen
	offset := CmnHdrLen + addrHdrLen
	//@ assert offset == CmnHdrLen + end_idx
	//@ assert slices.AbsSlice_Bytes(data, offset, len(data))
	// Decode path header.
	var err error
	hdrBytes := int(s.HdrLen) * LineLen
	pathLen := hdrBytes - CmnHdrLen - addrHdrLen
	if pathLen < 0 {
		//@ apply s.AddrHdrMem() --* (slices.AbsSlice_Bytes(data[CmnHdrLen:offset], 0, len(data[CmnHdrLen:offset])) && s.AddrHdrInitMem())
		//@ ghost slices.Unslice_Bytes(data, CmnHdrLen, offset, writePerm)
		//@ ghost slices.CombineAtIndex_Bytes(data, CmnHdrLen, len(data), offset, writePerm)
		//@ ghost slices.CombineAtIndex_Bytes(data, 0, len(data), CmnHdrLen, writePerm)
		//@ unfold s.AddrHdrInitMem()
		//@ fold s.NonInitMem()
		return serrors.New("invalid header, negative pathLen",
			"hdrBytes", int(hdrBytes), "addrHdrLen", int(addrHdrLen), "CmdHdrLen", int(CmnHdrLen))
	}
	//@ assert pathLen >= 0
	//@ assert addrHdrLen >= 0
	//@ assert CmnHdrLen == 12
	//@ assert 0 <= hdrBytes && hdrBytes >= (CmnHdrLen + addrHdrLen)
	if minLen := offset + pathLen; len(data) < minLen {
		df.SetTruncated()
		//@ apply s.AddrHdrMem() --* (slices.AbsSlice_Bytes(data[CmnHdrLen:offset], 0, len(data[CmnHdrLen:offset])) && s.AddrHdrInitMem())
		//@ ghost slices.Unslice_Bytes(data, CmnHdrLen, offset, writePerm)
		//@ ghost slices.CombineAtIndex_Bytes(data, CmnHdrLen, len(data), offset, writePerm)
		//@ ghost slices.CombineAtIndex_Bytes(data, 0, len(data), CmnHdrLen, writePerm)
		//@ unfold s.AddrHdrInitMem()
		//@ fold s.NonInitMem()
		return serrors.New("provided buffer is too small", "expected", int(minLen), "actual", int(len(data)))
	}
	//@ assert len(data) > CmnHdrLen
	//@ assert len(data) >= offset + pathLen
	//@ assert len(data) >= CmnHdrLen + addrHdrLen + pathLen
	//@ assert len(data) >= CmnHdrLen + addrHdrLen + (hdrBytes - CmnHdrLen - addrHdrLen)
	//@ assert len(data) >= hdrBytes
	//@ assert 0 <= hdrBytes && hdrBytes <= len(data)
	//@ ghost var pathMemLoc PathMemLoc
	//@ ghost s.hdrBytes = hdrBytes
	// NOTE XXX (gavinleroy) the following two variables (path & pathTYpe) should be removed
	// as soon as possible. Here is a brief explanation of why they are currently necessary.
	// In a magic wand instance `Q() --* P()` both the left and right-hand sides need
	// to be self framing. However, the instances received from the `s.getPath` method
	// are not. That is, you cannot say `Q(s.PathType) --* P()` because that would
	// not be self framing. Once Gobra introduces let-bindings, we could easily say
	// `let pt := s.PathType in (Q(pt) --* P())` which would be self framing. Though
	// demonstrated with the `s.PathType` field, this principle also applies for
	// `s.Path` which is also required in the use of the wands. Once a fix for this is
	// introduced, these variables should be removed, and all subsequent lines of the code
	// which were changed need to be updated.
	var path path.Path
	//@ ghost pathType := s.PathType
	path, err /*@, pathMemLoc @*/ = s.getPath(s.PathType)
	//@ assert (err == nil && pathMemLoc == Pool) ==> (s.PathPoolPartial(pathType) && s.PathPoolRawFull() && ((path.NonInitMem() && s.PathPoolPartial(pathType)) --* s.PathPoolFull()))
	//@ assert (err == nil && pathMemLoc == Raw) ==> (s.PathPoolFull() && s.PathPoolRawPartial() && ((path.NonInitMem() && s.PathPoolRawPartial()) --* s.PathPoolRawFull()))
	//@ assert s.PathType == pathType
	if err != nil {
		//@ apply s.AddrHdrMem() --* (slices.AbsSlice_Bytes(data[CmnHdrLen:offset], 0, len(data[CmnHdrLen:offset])) && s.AddrHdrInitMem())
		//@ ghost slices.Unslice_Bytes(data, CmnHdrLen, offset, writePerm)
		//@ ghost slices.CombineAtIndex_Bytes(data, CmnHdrLen, len(data), offset, writePerm)
		//@ ghost slices.CombineAtIndex_Bytes(data, 0, len(data), CmnHdrLen, writePerm)
		//@ unfold s.AddrHdrInitMem()
		//@ unfold s.PathPoolNone()
		//@ fold s.NonInitMem()
		return err
	}
	//@ assert acc(&s.Path)
	//@ assert path != nil
	//@ assert path.NonInitMem()
	//@ assert offset + pathLen <= len(data)
	//@ ghost slices.SplitByIndex_Bytes(data, offset, len(data), offset + pathLen, writePerm)
	//@ assert slices.AbsSlice_Bytes(data, 0, CmnHdrLen)
	// NOTE the slice [CmnHdrLen : offset] was consumed previously
	//@ assert slices.AbsSlice_Bytes(data, offset, offset + pathLen)
	//@ assert slices.AbsSlice_Bytes(data, offset + pathLen, len(data))
	//@ requires  acc(&s.Path)
	//@ requires  path != nil
	//@ requires  path.NonInitMem()
	//@ requires  slices.AbsSlice_Bytes(data, offset, offset + pathLen)
	//@ ensures   acc(&s.Path)
	//@ ensures   path != nil
	//@ ensures   err == nil ==> path.Mem()
	//@ ensures   err != nil ==> path.NonInitMem()
	//@ ensures   err != nil ==> err.ErrorMem()
	//@ ensures   err != nil ==> slices.AbsSlice_Bytes(data, offset, offset + pathLen)
	//@ decreases
	//@ outline(
	//@ ghost slices.Reslice_Bytes(data, offset, offset+pathLen, writePerm)
	// err = s.Path.DecodeFromBytes(data[offset : offset+pathLen])
	err = path.DecodeFromBytes(data[offset : offset+pathLen])
	//@ ghost if err != nil {
	//@   slices.Unslice_Bytes(data, offset, offset+pathLen, writePerm)
	//@ }
	//@ )
	if err != nil {
		//@ assert path.NonInitMem()
		//@ ghost if pathMemLoc == Pool {
		//@   assert s.PathPoolPartial(s.PathType)
		//@   assert s.PathPoolRawFull()
		//@   apply (path.NonInitMem() && s.PathPoolPartial(pathType)) --* s.PathPoolFull()
		//@   unfold s.PathPoolRawFull()
		//@   unfold s.PathPoolFull()
		//@ } else if pathMemLoc == Raw {
		//@   assert s.PathPoolFull()
		//@   assert s.PathPoolRawPartial()
		//@   apply (path.NonInitMem() && s.PathPoolRawPartial()) --* s.PathPoolRawFull()
		//@   unfold s.PathPoolRawFull()
		//@   unfold s.PathPoolFull()
		//@ } else {
		//@   assert pathMemLoc == New
		//@   assert s.PathPoolNone()
		//@   unfold s.PathPoolNone()
		//@ }
		//@ ghost slices.CombineAtIndex_Bytes(data, offset, len(data), offset+pathLen, writePerm)
		//@ apply s.AddrHdrMem() --* (slices.AbsSlice_Bytes(data[CmnHdrLen:offset], 0, len(data[CmnHdrLen:offset])) && s.AddrHdrInitMem())
		//@ ghost slices.Unslice_Bytes(data, CmnHdrLen, offset, writePerm)
		//@ ghost slices.CombineAtIndex_Bytes(data, CmnHdrLen, len(data), offset, writePerm)
		//@ ghost slices.CombineAtIndex_Bytes(data, 0, len(data), CmnHdrLen, writePerm)
		//@ unfold s.AddrHdrInitMem()
		//@ fold s.NonInitMem()
		return err
	}
	// NOTE XXX (gavinleroy) this assignment is necessary because the above
	// code was changed from using `s.Path` to the newly created local variable `path`.
	// The assignment should be REMOVED once the feature is addressed.
	//@ assert path.Mem()
	s.Path = path
	//@ assert s.Path.Mem()
	//@ assert s.Path != nil
	//@ ghost s.setPathLoc(pathMemLoc)
	//@ assert s.getPathLoc() == pathMemLoc
	//@ assert slices.AbsSlice_Bytes(data, 0, CmnHdrLen)
	// NOTE the slice [CmnHdrLen : offset] was consumed
	// NOTE the slice [offset : offset + pathLen] was consumed
	//@ assert slices.AbsSlice_Bytes(data, offset + pathLen, len(data))
	//@ requires  0 <= hdrBytes && hdrBytes <= len(data)
	//@ preserves acc(&s.Contents)
	//@ preserves acc(&s.Payload)
	//@ ensures   len(s.Contents) == hdrBytes
	//@ ensures   len(s.Payload) == len(data) - hdrBytes
	//@ decreases
	//@ outline (
	s.Contents = data[:hdrBytes]
	s.Payload = data[hdrBytes:]
	//@ )
	//@ unfold s.AddrHdrMem()
	//@ fold s.Mem()
	//@ s.SetUnderlyingBuf(data)
	return nil
}

// RecyclePaths enables recycling of paths used for DecodeFromBytes. This is
// only useful if the layer itself is reused.
// When this is enabled, the Path instance may be overwritten in
// DecodeFromBytes. No references to Path should be kept in use between
// invocations of DecodeFromBytes.
//@ preserves s.NonInitMem()
//@ ensures unfolding s.NonInitMem() in s.pathPool != nil
//@ decreases
func (s *SCION) RecyclePaths() {
	//@ unfold s.NonInitMem()
	//@ defer fold s.NonInitMem()
	if s.pathPool == nil {
		//@ ensures p_empty.NonInitMem()
		//@ decreases
		//@ outline(
		p_empty := empty.Path{}
		//@ fold p_empty.NonInitMem()
		//@ )
		//@ ensures p_onehop.NonInitMem()
		//@ decreases
		//@ outline(
		p_onehop := &onehop.Path{}
		//@ fold p_onehop.NonInitMem()
		//@ )
		//@ ensures p_raw.NonInitMem()
		//@ decreases
		//@ outline(
		p_raw := &scion.Raw{}
		//@ fold p_raw.Base.NonInitMem()
		//@ fold p_raw.NonInitMem()
		//@ )
		//@ ensures p_epic.NonInitMem()
		//@ decreases
		//@ outline(
		p_epic := &epic.Path{}
		//@ fold p_epic.NonInitMem()
		//@ )
		//@ assert int(empty.PathType) == 0
		//@ assert int(onehop.PathType) == 2
		//@ assert int(scion.PathType) == 1
		//@ assert int(epic.PathType) == 3
		s.pathPool = []path.Path{
			empty.PathType:  p_empty,
			onehop.PathType: p_onehop,
			scion.PathType:  p_raw,
			epic.PathType:   p_epic,
		}
		//@ assert len(s.pathPool) == 4
		//@ assert s.pathPool[0].NonInitMem()
		//@ assert s.pathPool[1].NonInitMem()
		//@ assert s.pathPool[2].NonInitMem()
		//@ assert s.pathPool[3].NonInitMem()
		s.pathPoolRaw = path.NewRawPath()
		//@ assert s.pathPoolRaw.NonInitMem()
	}
}

// getPath returns a new or recycled path for pathType
//@ requires  0 <= pathType && pathType < path.maxPathType
//@ requires  acc(&s.pathPoolRaw)
//@ requires  acc(&s.pathPool)
//@ requires  s.pathPool == nil ==> s.pathPoolRaw == nil
//@ requires  s.pathPool != nil ==> (forall i int :: 0 <= i && i < len(s.pathPool) ==> (acc(&s.pathPool[i]) && s.pathPool[i] != nil && s.pathPool[i].NonInitMem()))
//@ requires  s.pathPool != nil ==> (s.pathPoolRaw != nil && s.pathPoolRaw.NonInitMem())
//@ preserves acc(path.PathPackageMem(), definitions.ReadL20)
//@ ensures   err == nil ==> p != nil
//@ ensures   err == nil ==> p.NonInitMem()
//@ ensures   err == nil ==> isValidPathMemLoc(loc)
//@ ensures   (err == nil && loc == New) ==> s.PathPoolNone()
//@ ensures   (err == nil && loc == Pool) ==> (s.PathPoolPartial(pathType) && s.PathPoolRawFull() && ((p.NonInitMem() && s.PathPoolPartial(pathType)) --* s.PathPoolFull()))
//@ ensures   (err == nil && loc == Raw) ==> (s.PathPoolFull() && s.PathPoolRawPartial() && ((p.NonInitMem() && s.PathPoolRawPartial()) --* s.PathPoolRawFull()))
//@ ensures   err != nil ==> err.ErrorMem()
//@ ensures   err != nil ==> s.PathPoolNone()
//@ decreases
func (s *SCION) getPath(pathType path.Type) (p path.Path, err error /*@, ghost loc PathMemLoc @*/) {
	if s.pathPool == nil {
		p, tmp_e := path.NewPath(pathType)
		//@ fold s.PathPoolNone()
		return p, tmp_e /*@, New @*/
	}
	ipt := int(pathType)
	//@ assert 0 <= ipt
	if ipt < len(s.pathPool) {
		//@ loc := Pool
		p = s.pathPool[ipt]
		//@ fold s.PathPoolRawFull()
		//@ fold s.PathPoolPartial(pathType)
		//@ inhale (p.NonInitMem() && s.PathPoolPartial(pathType)) --* s.PathPoolFull()
		// NOTE XXX the following code should be used to package the magic wand, however, it is
		// not currently supported by Gobra. Here's a small description why:
		// The return value `p` is an interface, which in this situation is an alias of
		// `s.pathPoolRaw`. It is obvious that this alias exists due to the direct assignment
		// roughly 7 lines above. However, when the resources -- in the form of predicates --
		// are returned below, Gobra cannot show that `p` is still aliasing `s.pathPoolRaw`.
		// A logicaly solution would be to return the information that `p == s.pathPoolRaw`
		// when the returned `PathMemLoc, loc == Raw` but there is no way to (currently)
		// represent this as interfaces are not comparable.
		// Due to this, the following code will fail to verify saying that "permissions to
		// receiver s.pathPool[ipt] may be insufficient" when attempting to fold.
		// ```
		// package (p.NonInitMem() && s.PathPoolPartial(pathType)) --* s.PathPoolFull() {
		//   assert int(pathType) == ipt
		//   assert 0 <= ipt && ipt < len(s.pathPool)
		//   unfold s.PathPoolPartial(pathType)
		//   unfold p.NonInitMem()
		//   fold s.pathPool[ipt].NonInitMem()
		//   fold s.PathPoolFull()
		// }
		// ```
		return p, nil /*@, loc @*/
	}
	//@ fold s.PathPoolFull()
	p = s.pathPoolRaw
	//@ fold s.PathPoolRawPartial()
	//@ inhale (p.NonInitMem() && s.PathPoolRawPartial()) --* s.PathPoolRawFull()
	// NOTE XXX the following code should be used to package the magic wand, however, it is
	// not currently supported by Gobra. Here's a small description why:
	// The return value `p` is an interface, which in this situation is an alias of
	// `s.pathPoolRaw`. It is obvious that this alias exists due to the direct assignment
	// roughly 7 lines above. However, when the resources -- in the form of predicates --
	// are returned below, Gobra cannot show that `p` is still aliasing `s.pathPoolRaw`.
	// A logicaly solution would be to return the information that `p == s.pathPoolRaw`
	// when the returned `PathMemLoc, loc == Raw` but there is no way to (currently)
	// represent this as interfaces are not comparable.
	// Due to this, the following code will fail to verify saying that "permissions to
	// receiver s.pathPoolRaw may be insufficient" when attempting to fold.
	//
	// ```
	// package (p.NonInitMem() && s.PathPoolRawPartial()) --* s.PathPoolRawFull() {
	//   unfold s.PathPoolRawPartial()
	//   unfold p.NonInitMem()
	//   assert acc(&s.pathPoolRaw)
	//   fold s.pathPoolRaw.NonInitMem()
	//   fold s.PathPoolRawFull()
	// }
	// ```
	return p, nil /*@, Raw @*/
}

//@ trusted
//@ requires  slices.AbsSlice_Bytes(data, 0, len(data))
//@ preserves pb.Mem()
//@ ensures   e == nil ==> true
//@ ensures   e != nil ==> slices.AbsSlice_Bytes(data, 0, len(data))
//@ decreases
func decodeSCION(data []byte, pb gopacket.PacketBuilder) (e error) {
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
//@ decreases
func scionNextLayerType(t L4ProtocolType) gopacket.LayerType {
	return getTODOLayerType() // TODO FIXME
	// switch t {
	// case HopByHopClass:
	// 	return LayerTypeHopByHopExtn
	// case End2EndClass:
	// 	return LayerTypeEndToEndExtn
	// default:
	// 	return scionNextLayerTypeL4(t)
	// }
}

// scionNextLayerTypeAfterHBH returns the layer type for the given protocol
// identifier in a SCION hop-by-hop extension, excluding (repeated) hop-by-hop
// extensions.
//@ decreases
func scionNextLayerTypeAfterHBH(t L4ProtocolType) gopacket.LayerType {
	return getTODOLayerType() // TODO FIXME
	// switch t {
	// case HopByHopClass:
	// 	return gopacket.LayerTypeDecodeFailure
	// case End2EndClass:
	// 	return LayerTypeEndToEndExtn
	// default:
	// 	return scionNextLayerTypeL4(t)
	// }
}

// scionNextLayerTypeAfterE2E returns the layer type for the given protocol
// identifier, in a SCION end-to-end extension, excluding (repeated or
// misordered) hop-by-hop extensions or (repeated) end-to-end extensions.
//@ decreases
func scionNextLayerTypeAfterE2E(t L4ProtocolType) gopacket.LayerType {
	return getTODOLayerType() // TODO FIXME
	// switch t {
	// case HopByHopClass:
	// 	return gopacket.LayerTypeDecodeFailure
	// case End2EndClass:
	// 	return gopacket.LayerTypeDecodeFailure
	// default:
	// 	return scionNextLayerTypeL4(t)
	// }
}

// scionNextLayerTypeL4 returns the layer type for the given layer-4 protocol identifier.
// Does not handle extension header classes.
//@ decreases
func scionNextLayerTypeL4(t L4ProtocolType) gopacket.LayerType {
	return getTODOLayerType() // TODO FIXME
	// switch t {
	// case L4UDP:
	// 	return LayerTypeSCIONUDP
	// case L4SCMP:
	// 	return LayerTypeSCMP
	// case L4BFD:
	// 	return layerTypeBFD
	// default:
	// 	return gopacket.LayerTypePayload
	// }
}

// DstAddr parses the destination address into a net.Addr. The returned net.Addr references data
// from the underlaying layer data. Changing the net.Addr object might lead to inconsistent layer
// information and thus should be treated read-only. Instead, SetDstAddr should be used to update
// the destination address.
//@ trusted
//@ requires s.Mem()
//@ decreases
func (s *SCION) DstAddr() (net.Addr, error) {
	return parseAddr(s.DstAddrType, s.DstAddrLen, s.RawDstAddr)
}

// SrcAddr parses the source address into a net.Addr. The returned net.Addr references data from the
// underlaying layer data. Changing the net.Addr object might lead to inconsistent layer information
// and thus should be treated read-only. Instead, SetDstAddr should be used to update the source
// address.
//@ trusted // TODO FIXME
//@ decreases
func (s *SCION) SrcAddr() (net.Addr, error) {
	return parseAddr(s.SrcAddrType, s.SrcAddrLen, s.RawSrcAddr)
}

// SetDstAddr sets the destination address and updates the DstAddrLen/Type fields accordingly.
// SetDstAddr takes ownership of dst and callers should not write to it after calling SetDstAddr.
// Changes to dst might leave the layer in an inconsistent state.
//@ trusted // TODO FIXME
//@ decreases
func (s *SCION) SetDstAddr(dst net.Addr) error {
	var err error
	s.DstAddrLen, s.DstAddrType, s.RawDstAddr, err = packAddr(dst)
	return err
}

// SetSrcAddr sets the source address and updates the DstAddrLen/Type fields accordingly.
// SetSrcAddr takes ownership of src and callers should not write to it after calling SetSrcAddr.
// Changes to src might leave the layer in an inconsistent state.
//@ trusted // TODO FIXME
//@ decreases
func (s *SCION) SetSrcAddr(src net.Addr) error {
	var err error
	s.SrcAddrLen, s.SrcAddrType, s.RawSrcAddr, err = packAddr(src)
	return err
}

//@ requires addrLen == AddrLen4 ==> len(raw) == 4
//@ requires addrLen == AddrLen16 ==> len(raw) == 16
//@ requires acc(slices.AbsSlice_Bytes(raw, 0, len(raw)), definitions.ReadL20)
//@ ensures  addrLen != AddrLen4 && addrLen != AddrLen16 ==> err != nil
//@ ensures  (addrLen == AddrLen4 && (addrType == T4Ip || addrType == T4Svc)) ==> err == nil
//@ ensures  (addrLen == AddrLen16 && addrType == T16Ip) ==> err == nil
//@ ensures  err == nil ==> acc(resAddr.Mem(), definitions.ReadL20)
//@ ensures  err != nil ==> acc(slices.AbsSlice_Bytes(raw, 0, len(raw)), definitions.ReadL20)
//@ decreases
func parseAddr(addrType AddrType, addrLen AddrLen, raw []byte) (resAddr net.Addr, err error) {
	switch addrLen {
	case AddrLen4:
		switch addrType {
		case T4Ip:
			return &net.IPAddr{IP: net.IP(raw)}, nil
		case T4Svc:
			return addr.HostSVC(binary.BigEndian.Uint16(raw[:addr.HostLenSVC])), nil
		}
	case AddrLen16:
		switch addrType {
		case T16Ip:
			return &net.IPAddr{IP: net.IP(raw)}, nil
		}
	}
	return nil, serrors.New("unsupported address type/length combination",
		"type", addrType, "len", addrLen)
}

//@ trusted // TODO FIXME
//@ decreases
func packAddr(hostAddr net.Addr) (AddrLen, AddrType, []byte, error) {
	switch a := hostAddr.(type) {
	case *net.IPAddr:
		if ip := a.IP.To4(); ip != nil {
			return AddrLen4, T4Ip, ip, nil
		}
		return AddrLen16, T16Ip, a.IP, nil
	case addr.HostSVC:
		return AddrLen4, T4Svc, a.PackWithPad(2), nil
	}
	return 0, 0, nil, serrors.New("unsupported address", "addr", hostAddr)
}

// AddrHdrLen returns the length of the address header (destination and source ISD-AS-Host triples)
// in bytes.
//@ pure
//@ requires acc(&s.DstAddrLen, _)
//@ requires acc(&s.SrcAddrLen, _)
//@ requires s.DstAddrLen >= 0
//@ requires s.SrcAddrLen >= 0
//@ ensures  l == 2*addr.IABytes + addrBytes(s.DstAddrLen) + addrBytes(s.SrcAddrLen)
//@ ensures  addrBytes(s.DstAddrLen) >= 0
//@ ensures  addrBytes(s.SrcAddrLen) >= 0
//@ ensures  0 <= l
//@ decreases
func (s *SCION) AddrHdrLen() (l int) {
	return 2*addr.IABytes + addrBytes(s.DstAddrLen) + addrBytes(s.SrcAddrLen)
}

// SerializeAddrHdr serializes destination and source ISD-AS-Host address triples into the provided
// buffer. The caller must ensure that the correct address types and lengths are set in the SCION
// layer, otherwise the results of this method are undefined.
//@ requires  acc(s.AddrHdrMem(), definitions.ReadL2)
//@ preserves slices.AbsSlice_Bytes(buf, 0, len(buf))
//@ ensures   acc(s.AddrHdrMem(), definitions.ReadL2)
//@ ensures   err != nil ==> err.ErrorMem()
//@ decreases
func (s *SCION) SerializeAddrHdr(buf []byte) (err error) {
	//@ unfold acc(s.AddrHdrMem(), definitions.ReadL2)
	if len(buf) < s.AddrHdrLen() {
		//@ defer fold acc(s.AddrHdrMem(), definitions.ReadL2)
		return serrors.New("provided buffer is too small", "expected", s.AddrHdrLen(),
			"actual", len(buf))
	}
	dstAddrBytes := addrBytes(s.DstAddrLen)
	srcAddrBytes := addrBytes(s.SrcAddrLen)
	offset := 0
	//@ assert len(buf) >= 2*addr.IABytes + dstAddrBytes + srcAddrBytes
	//@ preserves 0 <= offset && offset + addr.IABytes < len(buf)
	//@ preserves  slices.AbsSlice_Bytes(buf, 0, len(buf))
	//@ preserves acc(&s.DstIA, definitions.ReadL2)
	//@ decreases
	//@ outline(
	//@ ghost slices.SplitByIndex_Bytes(buf, 0, len(buf), offset, writePerm)
	//@ ghost slices.Reslice_Bytes(buf, offset, len(buf), writePerm)
	//@ unfold slices.AbsSlice_Bytes(buf[offset:len(buf)], 0, len(buf[offset:len(buf)]))
	binary.BigEndian.PutUint64(buf[offset:], uint64(s.DstIA))
	//@ fold slices.AbsSlice_Bytes(buf[offset:], 0, len(buf[offset:len(buf)]))
	//@ ghost slices.Unslice_Bytes(buf, offset, len(buf), writePerm)
	//@ ghost slices.CombineAtIndex_Bytes(buf, 0, len(buf), offset, writePerm)
	//@ )
	offset += addr.IABytes
	//@ preserves 0 <= offset && offset + addr.IABytes < len(buf)
	//@ preserves acc(&s.SrcIA, definitions.ReadL2)
	//@ preserves slices.AbsSlice_Bytes(buf, 0, len(buf))
	//@ decreases
	//@ outline(
	//@ ghost slices.SplitByIndex_Bytes(buf, 0, len(buf), offset, writePerm)
	//@ ghost slices.Reslice_Bytes(buf, offset, len(buf), writePerm)
	//@ unfold slices.AbsSlice_Bytes(buf[offset:len(buf)], 0, len(buf[offset:len(buf)]))
	binary.BigEndian.PutUint64(buf[offset:], uint64(s.SrcIA))
	//@ fold slices.AbsSlice_Bytes(buf[offset:len(buf)], 0, len(buf[offset:len(buf)]))
	//@ ghost slices.Unslice_Bytes(buf, offset, len(buf), writePerm)
	//@ ghost slices.CombineAtIndex_Bytes(buf, 0, len(buf), offset, writePerm)
	//@ )
	offset += addr.IABytes
	//@ ghost slices.SplitByIndex_Bytes(buf, 0, len(buf), offset, writePerm)
	//@ ghost slices.SplitByIndex_Bytes(buf, offset, len(buf), offset+dstAddrBytes, writePerm)
	//@ requires  0 < dstAddrBytes
	//@ preserves 0 <= offset && offset + dstAddrBytes <= len(buf)
	//@ preserves acc(&s.RawDstAddr, definitions.ReadL2)
	//@ preserves acc(slices.AbsSlice_Bytes(s.RawDstAddr, 0, len(s.RawDstAddr)), definitions.ReadL2)
	//@ preserves slices.AbsSlice_Bytes(buf, offset, offset+dstAddrBytes)
	//@ decreases
	//@ outline (
	//@ ghost slices.Reslice_Bytes(buf, offset, offset+dstAddrBytes, writePerm)
	//@ unfold slices.AbsSlice_Bytes(buf[offset:offset+dstAddrBytes], 0, dstAddrBytes)
	//@ unfold acc(slices.AbsSlice_Bytes(s.RawDstAddr, 0, len(s.RawDstAddr)), definitions.ReadL2)
	copy(buf[offset:offset+dstAddrBytes], s.RawDstAddr /*@, definitions.ReadL2 @*/)
	//@ fold acc(slices.AbsSlice_Bytes(s.RawDstAddr, 0, len(s.RawDstAddr)), definitions.ReadL2)
	//@ fold slices.AbsSlice_Bytes(buf[offset:offset+dstAddrBytes], 0, dstAddrBytes)
	//@ assert offset < offset + dstAddrBytes
	//@ ghost slices.Unslice_Bytes(buf, offset, offset+dstAddrBytes, writePerm)
	//@ )
	//@ ghost slices.CombineAtIndex_Bytes(buf, 0, offset+dstAddrBytes, offset, writePerm)
	offset += dstAddrBytes
	//@ requires 0 <= offset && offset + srcAddrBytes <= len(buf)
	//@ requires 0 < srcAddrBytes
	//@ requires  slices.AbsSlice_Bytes(buf, 0, offset)
	//@ requires  slices.AbsSlice_Bytes(buf, offset, len(buf))
	//@ preserves acc(&s.RawSrcAddr, definitions.ReadL2)
	//@ preserves acc(slices.AbsSlice_Bytes(s.RawSrcAddr, 0, len(s.RawSrcAddr)), definitions.ReadL2)
	//@ ensures   slices.AbsSlice_Bytes(buf, 0, len(buf))
	//@ decreases
	//@ outline(
	//@ ghost slices.SplitByIndex_Bytes(buf, offset, len(buf), offset+srcAddrBytes, writePerm)
	//@ ghost slices.Reslice_Bytes(buf, offset, offset+srcAddrBytes, writePerm)
	//@ unfold slices.AbsSlice_Bytes(buf[offset:offset+srcAddrBytes], 0, len(buf[offset:offset+srcAddrBytes]))
	//@ unfold acc(slices.AbsSlice_Bytes(s.RawSrcAddr, 0, len(s.RawSrcAddr)), definitions.ReadL2)
	copy(buf[offset:offset+srcAddrBytes], s.RawSrcAddr /*@, definitions.ReadL2 @*/)
	//@ fold acc(slices.AbsSlice_Bytes(s.RawSrcAddr, 0, len(s.RawSrcAddr)), definitions.ReadL2)
	//@ fold slices.AbsSlice_Bytes(buf[offset:offset+srcAddrBytes], 0, len(buf[offset:offset+srcAddrBytes]))
	//@ ghost slices.Unslice_Bytes(buf, offset, offset+srcAddrBytes, writePerm)
	//@ ghost slices.CombineAtIndex_Bytes(buf, offset, len(buf), offset+srcAddrBytes, writePerm)
	//@ ghost slices.CombineAtIndex_Bytes(buf, 0, len(buf), offset, writePerm)
	//@ )
	//@ fold acc(s.AddrHdrMem(), definitions.ReadL2)
	return nil
}

// DecodeAddrHdr decodes the destination and source ISD-AS-Host address triples from the provided
// buffer. The caller must ensure that the correct address types and lengths are set in the SCION
// layer, otherwise the results of this method are undefined.

//@ requires  slices.AbsSlice_Bytes(data, 0, len(data))
//@ requires  s.AddrHdrInitMem()
// requires  acc(&s.RawDstAddr)
// requires  acc(&s.RawSrcAddr)
// requires  acc(&s.DstAddrLen)
// requires  acc(&s.SrcAddrLen)
// requires  acc(&s.SrcIA)
// requires  acc(&s.DstIA)
// requires  s.DstAddrLen >= 0
// requires  s.SrcAddrLen >= 0
//
//@ ensures   err == nil ==> s.AddrHdrMem()
//@ ensures   err == nil ==> end <= len(data)
//@ ensures   err == nil ==> end == (unfolding s.AddrHdrMem() in s.AddrHdrLen())
//@ ensures   err == nil ==> slices.AbsSlice_Bytes(data[end:], 0, len(data[end:]))
//@ ensures   err == nil ==> (s.AddrHdrMem() --* (slices.AbsSlice_Bytes(data[:end], 0, len(data[:end])) && s.AddrHdrInitMem()))
//
//@ ensures   err != nil ==> s.AddrHdrInitMem()
// ensures   err != nil ==> acc(&s.RawDstAddr)
// ensures   err != nil ==> acc(&s.RawSrcAddr)
// ensures   err != nil ==> acc(&s.DstAddrLen)
// ensures   err != nil ==> acc(&s.SrcAddrLen)
// ensures   err != nil ==> acc(&s.SrcIA)
// ensures   err != nil ==> acc(&s.DstIA)
//
//@ ensures   err != nil ==> slices.AbsSlice_Bytes(data, 0, len(data))
//@ ensures   err != nil ==> err.ErrorMem()
//@ decreases
func (s *SCION) DecodeAddrHdr(data []byte) (err error /*@, ghost end int @*/) {
	//@ unfold s.AddrHdrInitMem()
	if len(data) < s.AddrHdrLen() {
		//@ defer fold s.AddrHdrInitMem()
		return serrors.New("provided buffer is too small", "expected", s.AddrHdrLen(),
			"actual", int(len(data))) /*@, 0 @*/
	}
	//@ assert len(data) >= 2*addr.IABytes + addrBytes(s.DstAddrLen) + addrBytes(s.SrcAddrLen)
	offset := 0
	//@ requires 0 <= offset && offset + 8 < len(data)
	//@ preserves acc(&s.DstIA)
	//@ preserves slices.AbsSlice_Bytes(data, offset, len(data))
	//@ decreases
	//@ outline(
	//@ ghost slices.Reslice_Bytes(data, offset, len(data), writePerm)
	//@ unfold slices.AbsSlice_Bytes(data[offset:], 0, len(data[offset:]))
	s.DstIA = addr.IA(binary.BigEndian.Uint64(data[offset:]))
	//@ fold slices.AbsSlice_Bytes(data[offset:], 0, len(data[offset:]))
	//@ ghost slices.Unslice_Bytes(data, offset, len(data), writePerm)
	//@ )
	//@ ghost slices.SplitByIndex_Bytes(data, offset, len(data), offset+addr.IABytes, writePerm)
	offset += addr.IABytes
	//@ requires 0 <= offset && offset + 8 <= len(data)
	//@ preserves acc(&s.SrcIA)
	//@ preserves slices.AbsSlice_Bytes(data, offset, len(data))
	//@ decreases
	//@ outline(
	//@ ghost slices.Reslice_Bytes(data, offset, len(data), writePerm)
	//@ unfold slices.AbsSlice_Bytes(data[offset:], 0, len(data[offset:]))
	s.SrcIA = addr.IA(binary.BigEndian.Uint64(data[offset:]))
	//@ fold slices.AbsSlice_Bytes(data[offset:], 0, len(data[offset:]))
	//@ ghost slices.Unslice_Bytes(data, offset, len(data), writePerm)
	//@ )
	//@ ghost slices.SplitByIndex_Bytes(data, offset, len(data), offset+addr.IABytes, writePerm)
	//@ ghost slices.CombineAtIndex_Bytes(data, 0, offset+addr.IABytes, offset, writePerm)
	offset += addr.IABytes
	//@ assert slices.AbsSlice_Bytes(data, 0, offset)
	dstAddrBytes := addrBytes(s.DstAddrLen)
	srcAddrBytes := addrBytes(s.SrcAddrLen)
	//@ ghost slices.SplitByIndex_Bytes(data, offset, len(data), offset+dstAddrBytes, writePerm)
	//@ requires  0 <= offset && offset + dstAddrBytes <= len(data)
	//@ requires  slices.AbsSlice_Bytes(data, offset, offset+dstAddrBytes)
	//@ preserves acc(&s.RawDstAddr)
	//@ ensures   slices.AbsSlice_Bytes(s.RawDstAddr, 0, len(s.RawDstAddr))
	// ensures   s.RawDstAddr == data[offset : offset+dstAddrBytes]
	//@ decreases
	//@ outline(
	//@ ghost slices.Reslice_Bytes(data, offset, offset+dstAddrBytes, writePerm)
	//@ unfold slices.AbsSlice_Bytes(data[offset:offset+dstAddrBytes], 0, len(data[offset:offset+dstAddrBytes]))
	s.RawDstAddr = data[offset : offset+dstAddrBytes]
	//@ fold slices.AbsSlice_Bytes(s.RawDstAddr, 0, len(s.RawDstAddr))
	//@ )
	offset += dstAddrBytes
	//@ ghost slices.SplitByIndex_Bytes(data, offset, len(data), offset+srcAddrBytes, writePerm)
	//@ requires  0 <= offset && offset + srcAddrBytes <= len(data)
	//@ requires  slices.AbsSlice_Bytes(data, offset, offset+srcAddrBytes)
	//@ preserves acc(&s.RawSrcAddr)
	//@ ensures   slices.AbsSlice_Bytes(s.RawSrcAddr, 0, len(s.RawSrcAddr))
	// ensures   s.RawSrcAddr == data[offset : offset+srcAddrBytes]
	//@ decreases
	//@ outline(
	//@ ghost slices.Reslice_Bytes(data, offset, offset+srcAddrBytes, writePerm)
	//@ unfold slices.AbsSlice_Bytes(data[offset:offset+srcAddrBytes], 0, len(data[offset:offset+srcAddrBytes]))
	s.RawSrcAddr = data[offset : offset+srcAddrBytes]
	//@ fold slices.AbsSlice_Bytes(s.RawSrcAddr, 0, len(s.RawSrcAddr))
	//@ )
	//@ ghost end_idx := offset + srcAddrBytes
	//@ assert end_idx <= len(data)
	//@ assert end_idx == s.AddrHdrLen()
	//@ assert slices.AbsSlice_Bytes(data, offset + srcAddrBytes, len(data))
	//@ assert slices.AbsSlice_Bytes(data, end_idx, len(data))
	//@ ghost slices.Reslice_Bytes(data, end_idx, len(data), writePerm)
	//@ fold s.AddrHdrMem()
	//@ package (s.AddrHdrMem() --* (slices.AbsSlice_Bytes(data[:end_idx], 0, len(data[:end_idx])) && s.AddrHdrInitMem())) {
	//@   unfold s.AddrHdrMem()
	//    TODO FIXME
	//@   assume s.RawDstAddr === data[offset - dstAddrBytes : offset]
	//@   assume s.RawSrcAddr === data[offset : offset + srcAddrBytes]
	//
	//@   assert offset + srcAddrBytes == end_idx
	//@   assert slices.AbsSlice_Bytes(data, 0, offset - dstAddrBytes)
	//@   assert s.RawDstAddr === data[offset - dstAddrBytes : offset]
	//@   assert s.RawSrcAddr === data[offset : offset + srcAddrBytes]
	//@   unfold slices.AbsSlice_Bytes(s.RawDstAddr, 0, len(s.RawDstAddr))
	//@   fold slices.AbsSlice_Bytes(data[offset - dstAddrBytes : offset], 0, len(data[offset - dstAddrBytes : offset]))
	//@   ghost slices.Unslice_Bytes(data, offset - dstAddrBytes, offset, writePerm)
	//@   ghost slices.CombineAtIndex_Bytes(data, 0, offset, offset - dstAddrBytes, writePerm)
	//@   unfold slices.AbsSlice_Bytes(s.RawSrcAddr, 0, len(s.RawSrcAddr))
	//@   fold slices.AbsSlice_Bytes(data[offset : offset + srcAddrBytes], 0, len(data[offset : offset + srcAddrBytes]))
	//@   ghost slices.Unslice_Bytes(data, offset, offset + srcAddrBytes, writePerm)
	//@   ghost slices.CombineAtIndex_Bytes(data, 0, offset + srcAddrBytes, offset, writePerm)
	//@   assert slices.AbsSlice_Bytes(data, 0, end_idx)
	//@   ghost slices.Reslice_Bytes(data, 0, end_idx, writePerm)
	//@   fold s.AddrHdrInitMem()
	//@ }
	return nil /*@, end_idx @*/
}

//@ pure
//@ requires addrLen >= 0
//@ ensures  l == (int(addrLen) + 1) * LineLen
//@ ensures  addrLen == AddrLen4 ==> l == 4
//@ ensures  addrLen == AddrLen8 ==> l == 8
//@ ensures  addrLen == AddrLen12 ==> l == 12
//@ ensures  addrLen == AddrLen16 ==> l == 16
//@ ensures  l > 0 && l % 2 == 0
//@ decreases
func addrBytes(addrLen AddrLen) (l int) {
	return (int(addrLen) + 1) * LineLen
}

// computeChecksum computes the checksum with the SCION pseudo header.
//@ preserves s != nil ==> acc(s.Mem(), definitions.ReadL10)
//@ preserves acc(slices.AbsSlice_Bytes(upperLayer, 0, len(upperLayer)), definitions.ReadL10)
//@ ensures s == nil ==> retErr != nil
//@ ensures retErr != nil ==> ret == 0
//@ ensures s != nil && s.getLenRawSrcAddr() > 0 && s.getLenRawDstAddr() > 0 ==> retErr == nil
//@ decreases
func (s *SCION) computeChecksum(upperLayer []byte, protocol uint8) (ret uint16, retErr error) {
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

//@ preserves acc(s.Mem(), definitions.ReadL10)
//@ ensures   s.getLenRawSrcAddr() == 0 ==> resErr != nil
//@ ensures   s.getLenRawDstAddr() == 0 ==> resErr != nil
//@ ensures   s.getLenRawSrcAddr() > 0 && s.getLenRawDstAddr() > 0 ==> resErr == nil
//@ decreases
func (s *SCION) pseudoHeaderChecksum(length int, protocol uint8) (res uint32, resErr error) {
	if /*@ unfolding acc(s.Mem(), definitions.ReadL20) in @*/ len(s.RawDstAddr) == 0 {
		return 0, serrors.New("destination address missing")
	}
	if /*@ unfolding acc(s.Mem(), definitions.ReadL20) in @*/ len(s.RawSrcAddr) == 0 {
		return 0, serrors.New("source address missing")
	}
	var csum uint32
	var srcIA /*@@@*/, dstIA /*@@@*/ [8]byte
	//@ preserves acc(s.Mem(), definitions.ReadL15)
	//@ preserves forall i int :: 0 <= i && i < 8 ==> acc(&srcIA[i])
	//@ decreases
	//@ outline(
	//@ unfold acc(s.Mem(), definitions.ReadL20)
	binary.BigEndian.PutUint64(srcIA[:], uint64(s.SrcIA))
	//@ fold acc(s.Mem(), definitions.ReadL20)
	//@ )
	//@ preserves acc(s.Mem(), definitions.ReadL15)
	//@ preserves forall i int :: 0 <= i && i < 8 ==> acc(&dstIA[i])
	//@ decreases
	//@ outline(
	//@ unfold acc(s.Mem(), definitions.ReadL20)
	binary.BigEndian.PutUint64(dstIA[:], uint64(s.DstIA))
	//@ fold acc(s.Mem(), definitions.ReadL20)
	//@ )
	//@ invariant 0 <= i && i <= 8
	//@ invariant i % 2 == 0
	//@ invariant forall i int :: 0 <= i && i < 8 ==> acc(&srcIA[i])
	//@ invariant forall i int :: 0 <= i && i < 8 ==> acc(&dstIA[i])
	//@ decreases 8 - i
	for i := 0; i < 8; i += 2 {
		csum += uint32(srcIA[i]) << 8
		csum += uint32(srcIA[i+1])
		csum += uint32(dstIA[i]) << 8
		csum += uint32(dstIA[i+1])
	}
	// Address length is guaranteed to be a multiple of 2 by the protocol.
	//@ ghost rawSrcAddrLen := unfolding acc(s.Mem(), definitions.ReadL15) in len(s.RawSrcAddr)
	//@ assume rawSrcAddrLen % 2 == 0 // TODO FIXME
	//
	//@ invariant acc(s.Mem(), definitions.ReadL15)
	//@ invariant rawSrcAddrLen == (unfolding acc(s.Mem(), definitions.ReadL15) in len(s.RawSrcAddr))
	//@ invariant 0 <= i && i <= rawSrcAddrLen
	//@ invariant i % 2 == 0
	//@ decreases rawSrcAddrLen - i
	for i := 0; i < /*@unfolding acc(s.Mem(), definitions.ReadL15) in@*/ len(s.RawSrcAddr); i += 2 {
		//@ requires 0 <= i && i + 1 < rawSrcAddrLen
		//@ requires i % 2 == 0
		//@ preserves acc(s.Mem(), definitions.ReadL20)
		//@ ensures i == before(i)
		//@ decreases
		//@ outline(
		//@ unfold acc(s.Mem(), definitions.ReadL20)
		//@ unfold acc(slices.AbsSlice_Bytes(s.RawSrcAddr, 0, len(s.RawSrcAddr)), definitions.ReadL20)
		csum += uint32(s.RawSrcAddr[i]) << 8
		csum += uint32(s.RawSrcAddr[i+1])
		//@ fold acc(slices.AbsSlice_Bytes(s.RawSrcAddr, 0, len(s.RawSrcAddr)), definitions.ReadL20)
		//@ fold acc(s.Mem(), definitions.ReadL20)
		//@ )
	}
	//@ ghost rawDstAddrLen := unfolding acc(s.Mem(), definitions.ReadL15) in len(s.RawDstAddr)
	//@ assume rawDstAddrLen % 2 == 0 // TODO FIXME
	//
	//@ invariant acc(s.Mem(), definitions.ReadL15)
	//@ invariant rawDstAddrLen == (unfolding acc(s.Mem(), definitions.ReadL15) in len(s.RawDstAddr))
	//@ invariant 0 <= i && i <= rawDstAddrLen
	//@ invariant i % 2 == 0
	//@ decreases rawDstAddrLen - i
	for i := 0; i < /*@unfolding acc(s.Mem(), definitions.ReadL15) in@*/ len(s.RawDstAddr); i += 2 {
		//@ requires 0 <= i && i + 1 < rawDstAddrLen
		//@ requires i % 2 == 0
		//@ preserves acc(s.Mem(), definitions.ReadL20)
		//@ ensures i == before(i)
		//@ decreases
		//@ outline(
		//@ unfold acc(s.Mem(), definitions.ReadL20)
		//@ unfold acc(slices.AbsSlice_Bytes(s.RawDstAddr, 0, len(s.RawDstAddr)), definitions.ReadL20)
		csum += uint32(s.RawDstAddr[i]) << 8
		csum += uint32(s.RawDstAddr[i+1])
		//@ fold acc(slices.AbsSlice_Bytes(s.RawDstAddr, 0, len(s.RawDstAddr)), definitions.ReadL20)
		//@ fold acc(s.Mem(), definitions.ReadL20)
		//@ )
	}
	l := uint32(length)
	csum += (l >> 16) + (l & 0xffff)
	csum += uint32(protocol)
	return csum, nil
}

//@ preserves acc(slices.AbsSlice_Bytes(upperLayer, 0, len(upperLayer)), definitions.ReadL15)
//@ decreases
func (s *SCION) upperLayerChecksum(upperLayer []byte, csum uint32) uint32 {
	// Compute safe boundary to ensure we do not access out of bounds.
	// Odd lengths are handled at the end.
	safeBoundary := len(upperLayer) - 1
	//@ unfold acc(slices.AbsSlice_Bytes(upperLayer, 0, len(upperLayer)), definitions.ReadL20)
	//@ invariant 0 <= i && i < safeBoundary + 2
	//@ invariant i % 2 == 0
	//@ invariant len(upperLayer) - 1 == safeBoundary
	//@ invariant forall i int :: 0 <= i && i < len(upperLayer) ==> acc(&upperLayer[i], definitions.ReadL20)
	//@ decreases safeBoundary - i
	for i := 0; i < safeBoundary; i += 2 {
		csum += uint32(upperLayer[i]) << 8
		csum += uint32(upperLayer[i+1])
	}
	if len(upperLayer)%2 == 1 {
		csum += uint32(upperLayer[safeBoundary]) << 8
	}
	//@ fold acc(slices.AbsSlice_Bytes(upperLayer, 0, len(upperLayer)), definitions.ReadL20)
	return csum
}

//@ trusted
//@ decreases
func (s *SCION) foldChecksum(csum uint32) uint16 {
	for csum > 0xffff {
		csum = (csum >> 16) + (csum & 0xffff)
	}
	return ^uint16(csum)
}
