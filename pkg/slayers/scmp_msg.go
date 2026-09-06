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

package slayers

import (
	"encoding/binary"

	"github.com/google/gopacket"

	"github.com/scionproto/scion/pkg/addr"
	"github.com/scionproto/scion/pkg/private/serrors"
	// @ . "github.com/scionproto/scion/verification/utils/definitions"
	// @ sl "github.com/scionproto/scion/verification/utils/slices"
)

const scmpRawInterfaceLen = 8

// SCMPExternalInterfaceDown message contains the data for that error.
//
//	 0                   1                   2                   3
//	 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
//	+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//	|              ISD              |                               |
//	+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+         AS                    +
//	|                                                               |
//	+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//	|                                                               |
//	+                        Interface ID                           +
//	|                                                               |
//	+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
type SCMPExternalInterfaceDown struct {
	BaseLayer
	IA   addr.IA
	IfID uint64
}

// LayerType returns LayerTypeSCMPExternalInterfaceDown
// @ pure
// @ decreases
func (i *SCMPExternalInterfaceDown) LayerType() gopacket.LayerType {
	return LayerTypeSCMPExternalInterfaceDown
}

// NextLayerType returns the layer type contained by this DecodingLayer.
// @ decreases
func (i *SCMPExternalInterfaceDown) NextLayerType() gopacket.LayerType {
	return gopacket.LayerTypePayload
}

// DecodeFromBytes decodes the given bytes into this layer.
// @ requires  df != nil
// @ requires  i.NonInitMem()
// @ requires  sl.Bytes(data, 0, len(data))
// @ preserves df.Mem()
// @ ensures   res == nil ==> i.Mem(data)
// @ ensures   res != nil ==> (i.NonInitMem() && sl.Bytes(data, 0, len(data)))
// @ ensures   res != nil ==> res.ErrorMem()
// @ decreases
func (i *SCMPExternalInterfaceDown) DecodeFromBytes(data []byte,
	df gopacket.DecodeFeedback) (res error) {

	minLength := addr.IABytes + scmpRawInterfaceLen
	if size := len(data); size < minLength {
		df.SetTruncated()
		return serrors.New("buffer too short", "mininum_legth", minLength, "actual", size)
	}
	// @ unfold i.NonInitMem()
	offset := 0
	// the reads only need element permissions, so the buffer is unfolded once
	// @ unfold sl.Bytes(data, 0, len(data))
	// @ assert forall k int :: { &data[offset:][k] } 0 <= k && k < len(data[offset:]) ==>
	// @ 	&data[offset:][k] == &data[offset+k]
	i.IA = addr.IA(binary.BigEndian.Uint64(data[offset:]))
	offset += addr.IABytes
	// @ sl.AssertSliceOverlap(data, offset, offset+scmpRawInterfaceLen)
	i.IfID = binary.BigEndian.Uint64(data[offset : offset+scmpRawInterfaceLen])
	// @ fold sl.Bytes(data, 0, len(data))
	offset += scmpRawInterfaceLen
	i.BaseLayer = BaseLayer{
		Contents: data[:offset],
		Payload:  data[offset:],
	}
	// @ fold i.BaseLayer.Mem(data, addr.IABytes+scmpRawInterfaceLen)
	// @ fold i.Mem(data)
	return nil
}

// SerializeTo writes the serialized form of this layer into the
// SerializationBuffer, implementing gopacket.SerializableLayer.
// @ requires  b != nil
// @ requires  i.Mem(ubufMem)
// @ preserves b.Mem()
// @ preserves sl.Bytes(b.UBuf(), 0, len(b.UBuf()))
// @ ensures   err == nil ==> i.Mem(ubufMem)
// @ ensures   err != nil ==> err.ErrorMem()
// @ decreases
func (i *SCMPExternalInterfaceDown) SerializeTo(b gopacket.SerializeBuffer, opts gopacket.SerializeOptions /*@, ghost ubufMem []byte @*/) (err error) {

	buf, err := b.PrependBytes(addr.IABytes + scmpRawInterfaceLen)
	if err != nil {
		return err
	}
	// @ ghost underlyingBufRes := b.UBuf()
	offset := 0
	// @ unfold i.Mem(ubufMem)
	// @ defer fold i.Mem(ubufMem)
	// @ assert buf === underlyingBufRes[:addr.IABytes+scmpRawInterfaceLen]
	// the writes only need element permissions, so the buffer is unfolded once
	// @ unfold sl.Bytes(underlyingBufRes, 0, len(underlyingBufRes))
	// @ assert forall k int :: { &buf[k] } { &underlyingBufRes[k] } 0 <= k && k < len(buf) ==> &buf[k] == &underlyingBufRes[k]
	// @ assert forall k int :: { &buf[offset:][k] } 0 <= k && k < len(buf[offset:]) ==>
	// @ 	&buf[offset:][k] == &buf[offset+k]
	binary.BigEndian.PutUint64(buf[offset:], uint64(i.IA))
	offset += addr.IABytes
	// @ sl.AssertSliceOverlap(buf, offset, offset+scmpRawInterfaceLen)
	binary.BigEndian.PutUint64(buf[offset:offset+scmpRawInterfaceLen], i.IfID)
	// @ fold sl.Bytes(underlyingBufRes, 0, len(underlyingBufRes))
	return nil
}

// @ requires pb != nil
// @ preserves pb.Mem()
// @ requires sl.Bytes(data, 0, len(data))
// @ ensures res != nil ==> res.ErrorMem()
// @ decreases
func decodeSCMPExternalInterfaceDown(data []byte, pb gopacket.PacketBuilder) (res error) {
	s := &SCMPExternalInterfaceDown{}
	// @ fold s.NonInitMem()
	err := s.DecodeFromBytes(data, pb)
	if err != nil {
		return err
	}
	pb.AddLayer(s)
	verScionTmp := gopacket.LayerTypePayload
	// @ fold verScionTmp.Mem()
	return pb.NextDecoder(verScionTmp)
}

// SCMPInternalConnectivityDown indicates the AS internal connection between 2
// routers is down. The format is as follows:
//
//	 0                   1                   2                   3
//	 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
//	+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//	|              ISD              |                               |
//	+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+         AS                    +
//	|                                                               |
//	+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//	|                                                               |
//	+                   Ingress Interface ID                        +
//	|                                                               |
//	+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//	|                                                               |
//	+                   Egress Interface ID                         +
//	|                                                               |
//	+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
type SCMPInternalConnectivityDown struct {
	BaseLayer

	IA      addr.IA
	Ingress uint64
	Egress  uint64
}

// LayerType returns LayerTypeSCMPInternalConnectivityDown.
// @ decreases
// @ pure
func (i *SCMPInternalConnectivityDown) LayerType() gopacket.LayerType {
	return LayerTypeSCMPInternalConnectivityDown
}

// NextLayerType returns the layer type contained by this DecodingLayer.
// @ decreases
// @ pure
func (*SCMPInternalConnectivityDown) NextLayerType() gopacket.LayerType {
	return gopacket.LayerTypePayload
}

// DecodeFromBytes decodes the given bytes into this layer.
// @ requires  df != nil
// @ requires  sl.Bytes(data, 0, len(data))
// @ requires  i.NonInitMem()
// @ preserves df.Mem()
// @ ensures   res == nil ==> i.Mem(data)
// @ ensures   res != nil ==> (i.NonInitMem() && sl.Bytes(data, 0, len(data)))
// @ ensures   res != nil ==> res.ErrorMem()
// @ decreases
func (i *SCMPInternalConnectivityDown) DecodeFromBytes(data []byte,
	df gopacket.DecodeFeedback) (res error) {

	minLength := addr.IABytes + 2*scmpRawInterfaceLen
	if size := len(data); size < minLength {
		df.SetTruncated()
		return serrors.New("buffer too short", "mininum_legth", minLength, "actual", size)
	}
	// @ unfold i.NonInitMem()
	// @ defer fold i.Mem(data)
	offset := 0
	// the reads only need element permissions, so the buffer is unfolded once
	// @ unfold sl.Bytes(data, 0, len(data))
	// @ assert forall k int :: { &data[offset:][k] } 0 <= k && k < len(data[offset:]) ==>
	// @ 	&data[offset:][k] == &data[offset+k]
	i.IA = addr.IA(binary.BigEndian.Uint64(data[offset:]))
	offset += addr.IABytes
	// @ sl.AssertSliceOverlap(data, offset, offset+scmpRawInterfaceLen)
	i.Ingress = binary.BigEndian.Uint64(data[offset : offset+scmpRawInterfaceLen])
	offset += scmpRawInterfaceLen
	// @ sl.AssertSliceOverlap(data, offset, offset+scmpRawInterfaceLen)
	i.Egress = binary.BigEndian.Uint64(data[offset : offset+scmpRawInterfaceLen])
	// @ fold sl.Bytes(data, 0, len(data))
	offset += scmpRawInterfaceLen
	i.BaseLayer = BaseLayer{
		Contents: data[:offset],
		Payload:  data[offset:],
	}
	// @ fold i.BaseLayer.Mem(data, addr.IABytes+2*scmpRawInterfaceLen)
	return nil
}

// SerializeTo writes the serialized form of this layer into the
// SerializationBuffer, implementing gopacket.SerializableLayer.
// @ requires  b != nil
// @ requires  i.Mem(ubufMem)
// @ preserves b.Mem()
// @ preserves sl.Bytes(b.UBuf(), 0, len(b.UBuf()))
// @ ensures   err == nil ==> i.Mem(ubufMem)
// @ ensures   err != nil ==> err.ErrorMem()
// @ decreases
func (i *SCMPInternalConnectivityDown) SerializeTo(b gopacket.SerializeBuffer, opts gopacket.SerializeOptions /*@, ghost ubufMem []byte @*/) (err error) {

	buf, err := b.PrependBytes(addr.IABytes + 2*scmpRawInterfaceLen)
	// @ ghost underlyingBufRes := b.UBuf()
	if err != nil {
		return err
	}
	offset := 0
	// @ unfold i.Mem(ubufMem)
	// @ defer fold i.Mem(ubufMem)
	// @ assert buf === underlyingBufRes[:addr.IABytes+2*scmpRawInterfaceLen]
	// the writes only need element permissions, so the buffer is unfolded once
	// @ unfold sl.Bytes(underlyingBufRes, 0, len(underlyingBufRes))
	// @ assert forall k int :: { &buf[k] } { &underlyingBufRes[k] } 0 <= k && k < len(buf) ==> &buf[k] == &underlyingBufRes[k]
	// @ assert forall k int :: { &buf[offset:][k] } 0 <= k && k < len(buf[offset:]) ==>
	// @ 	&buf[offset:][k] == &buf[offset+k]
	binary.BigEndian.PutUint64(buf[offset:], uint64(i.IA))
	offset += addr.IABytes
	// @ sl.AssertSliceOverlap(buf, offset, offset+scmpRawInterfaceLen)
	binary.BigEndian.PutUint64(buf[offset:offset+scmpRawInterfaceLen], i.Ingress)
	offset += scmpRawInterfaceLen
	// @ sl.AssertSliceOverlap(buf, offset, offset+scmpRawInterfaceLen)
	binary.BigEndian.PutUint64(buf[offset:offset+scmpRawInterfaceLen], i.Egress)
	// @ fold sl.Bytes(underlyingBufRes, 0, len(underlyingBufRes))
	return nil
}

// @ requires pb != nil
// @ preserves pb.Mem()
// @ requires sl.Bytes(data, 0, len(data))
// @ ensures err != nil ==> err.ErrorMem()
// @ decreases
func decodeSCMPInternalConnectivityDown(data []byte, pb gopacket.PacketBuilder) (err error) {
	s := &SCMPInternalConnectivityDown{}
	// @ fold s.NonInitMem()
	if err := s.DecodeFromBytes(data, pb); err != nil {
		return err
	}
	pb.AddLayer(s)
	verScionTmp := s.NextLayerType()
	// @ fold verScionTmp.Mem()
	return pb.NextDecoder(verScionTmp)
}

// SCMPEcho represents the structure of a ping.
//
//	 0                   1                   2                   3
//	 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
//	+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//	|           Identifier          |        Sequence Number        |
//	+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
type SCMPEcho struct {
	BaseLayer

	Identifier uint16
	SeqNumber  uint16
}

// LayerType returns LayerTypeSCMPEcho.
// @ decreases
// @ pure
func (i *SCMPEcho) LayerType() gopacket.LayerType {
	return LayerTypeSCMPEcho
}

// NextLayerType returns the layer type contained by this DecodingLayer.
// @ decreases
// @ pure
func (*SCMPEcho) NextLayerType() gopacket.LayerType {
	return gopacket.LayerTypePayload
}

// DecodeFromBytes decodes the given bytes into this layer.
// @ requires  df != nil
// @ requires  i.NonInitMem()
// @ requires  sl.Bytes(data, 0, len(data))
// @ preserves df.Mem()
// @ ensures   res == nil ==> i.Mem(data)
// @ ensures   res != nil ==> (i.NonInitMem() && sl.Bytes(data, 0, len(data)))
// @ ensures   res != nil ==> res.ErrorMem()
// @ decreases
func (i *SCMPEcho) DecodeFromBytes(data []byte, df gopacket.DecodeFeedback) (res error) {
	minLength := 4
	if size := len(data); size < minLength {
		df.SetTruncated()
		return serrors.New("buffer too short", "min", minLength, "actual", size)
	}
	// @ unfold i.NonInitMem()
	// @ defer fold i.Mem(data)
	offset := 0
	// the reads only need element permissions, so the buffer is unfolded once
	// @ unfold sl.Bytes(data, 0, len(data))
	// @ assert &data[:2][0] == &data[0] && &data[:2][1] == &data[1]
	i.Identifier = binary.BigEndian.Uint16(data[:2])
	offset += 2
	// @ assert &data[offset : offset+2][0] == &data[offset]
	// @ assert &data[offset : offset+2][1] == &data[offset+1]
	i.SeqNumber = binary.BigEndian.Uint16(data[offset : offset+2])
	// @ fold sl.Bytes(data, 0, len(data))
	offset += 2
	i.BaseLayer = BaseLayer{
		Contents: data[:offset],
		Payload:  data[offset:],
	}
	// @ fold i.BaseLayer.Mem(data, 4)
	return nil
}

// SerializeTo writes the serialized form of this layer into the
// SerializationBuffer, implementing gopacket.SerializableLayer.
// @ requires  b != nil
// @ requires  i.Mem(ubufMem)
// @ preserves b.Mem()
// @ preserves sl.Bytes(b.UBuf(), 0, len(b.UBuf()))
// @ ensures   err == nil ==> i.Mem(ubufMem)
// @ ensures   err != nil ==> err.ErrorMem()
// @ decreases
func (i *SCMPEcho) SerializeTo(b gopacket.SerializeBuffer, opts gopacket.SerializeOptions /*@, ghost ubufMem []byte @*/) (err error) {
	buf, err := b.PrependBytes(4)
	// @ ghost underlyingBufRes :=b.UBuf()
	if err != nil {
		return err
	}
	offset := 0
	// @ unfold i.Mem(ubufMem)
	// @ defer fold i.Mem(ubufMem)
	// @ assert buf === underlyingBufRes[:4]
	// the writes only need element permissions, so the buffer is unfolded once
	// @ unfold sl.Bytes(underlyingBufRes, 0, len(underlyingBufRes))
	// @ assert forall k int :: { &buf[k] } { &underlyingBufRes[k] } 0 <= k && k < len(buf) ==> &buf[k] == &underlyingBufRes[k]
	// @ assert &buf[:2][0] == &buf[0] && &buf[:2][1] == &buf[1]
	binary.BigEndian.PutUint16(buf[:2], i.Identifier)
	offset += 2
	// @ assert &buf[offset : offset+2][0] == &buf[offset]
	// @ assert &buf[offset : offset+2][1] == &buf[offset+1]
	binary.BigEndian.PutUint16(buf[offset:offset+2], i.SeqNumber)
	// @ fold sl.Bytes(underlyingBufRes, 0, len(underlyingBufRes))
	return nil
}

// @ requires pb != nil
// @ preserves pb.Mem()
// @ requires sl.Bytes(data, 0, len(data))
// @ ensures err != nil ==> err.ErrorMem()
// @ decreases
func decodeSCMPEcho(data []byte, pb gopacket.PacketBuilder) (err error) {
	s := &SCMPEcho{}
	// @ fold s.NonInitMem()
	if err := s.DecodeFromBytes(data, pb); err != nil {
		return err
	}
	pb.AddLayer(s)
	verScionTmp := s.NextLayerType()
	// @ fold verScionTmp.Mem()
	return pb.NextDecoder(verScionTmp)
}

// SCMPParameterProblem represents the structure of a parameter problem message.
//
//	+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//	|            reserved           |           Pointer             |
//	+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
type SCMPParameterProblem struct {
	BaseLayer
	Pointer uint16
}

// LayerType returns LayerTypeSCMPParameterProblem.
// @ decreases
// @ pure
func (i *SCMPParameterProblem) LayerType() gopacket.LayerType {
	return LayerTypeSCMPParameterProblem
}

// NextLayerType returns the layer type contained by this DecodingLayer.
// @ decreases
// @ pure
func (*SCMPParameterProblem) NextLayerType() gopacket.LayerType {
	return gopacket.LayerTypePayload
}

// DecodeFromBytes decodes the given bytes into this layer.
// @ requires  df != nil
// @ requires  i.NonInitMem()
// @ requires  sl.Bytes(data, 0, len(data))
// @ preserves df.Mem()
// @ ensures   res == nil ==> i.Mem(data)
// @ ensures   res != nil ==> (i.NonInitMem() && sl.Bytes(data, 0, len(data)))
// @ ensures   res != nil ==> res.ErrorMem()
// @ decreases
func (i *SCMPParameterProblem) DecodeFromBytes(data []byte, df gopacket.DecodeFeedback) (res error) {
	minLength := 2 + 2
	if size := len(data); size < minLength {
		df.SetTruncated()
		return serrors.New("buffer too short", "min", minLength, "actual", size)
	}
	// @ unfold i.NonInitMem()
	// @ defer fold i.Mem(data)
	// the read only needs element permissions, so the buffer is unfolded once
	// @ unfold sl.Bytes(data, 0, len(data))
	// @ assert &data[2:4][0] == &data[2]
	// @ assert &data[2:4][1] == &data[3]
	i.Pointer = binary.BigEndian.Uint16(data[2:4])
	// @ fold sl.Bytes(data, 0, len(data))
	i.BaseLayer = BaseLayer{
		Contents: data[:4],
		Payload:  data[4:],
	}
	// @ fold i.BaseLayer.Mem(data, 4)
	return nil
}

// SerializeTo writes the serialized form of this layer into the
// SerializationBuffer, implementing gopacket.SerializableLayer.
// @ requires  b != nil
// @ requires  i.Mem(ubufMem)
// @ preserves b.Mem()
// @ preserves sl.Bytes(b.UBuf(), 0, len(b.UBuf()))
// @ ensures   err == nil ==> i.Mem(ubufMem)
// @ ensures   err != nil ==> err.ErrorMem()
// @ decreases
func (i *SCMPParameterProblem) SerializeTo(b gopacket.SerializeBuffer, opts gopacket.SerializeOptions /*@, ghost ubufMem []byte @*/) (err error) {

	buf, err := b.PrependBytes(2 + 2)
	// @ ghost underlyingBufRes := b.UBuf()
	if err != nil {
		return err
	}
	// @ unfold i.Mem(ubufMem)
	// @ defer fold i.Mem(ubufMem)
	// @ assert buf === underlyingBufRes[:2+2]
	// the writes only need element permissions, so the buffer is unfolded once
	// @ unfold sl.Bytes(underlyingBufRes, 0, len(underlyingBufRes))
	// @ assert forall k int :: { &buf[k] } { &underlyingBufRes[k] } 0 <= k && k < len(buf) ==> &buf[k] == &underlyingBufRes[k]
	// @ assert &buf[0:2][0] == &buf[0] && &buf[0:2][1] == &buf[1]
	binary.BigEndian.PutUint16(buf[0:2], uint16(0)) //Reserved
	// @ assert &buf[2:4][0] == &buf[2]
	// @ assert &buf[2:4][1] == &buf[3]
	binary.BigEndian.PutUint16(buf[2:4], i.Pointer)
	// @ fold sl.Bytes(underlyingBufRes, 0, len(underlyingBufRes))
	return nil
}

// @ requires  pb != nil
// @ preserves pb.Mem()
// @ requires  sl.Bytes(data, 0, len(data))
// @ ensures   err != nil ==> err.ErrorMem()
// @ decreases
func decodeSCMPParameterProblem(data []byte, pb gopacket.PacketBuilder) (err error) {
	s := &SCMPParameterProblem{}
	// @ fold s.NonInitMem()
	if err := s.DecodeFromBytes(data, pb); err != nil {
		return err
	}
	pb.AddLayer(s)
	verScionTmp := s.NextLayerType()
	// @ fold verScionTmp.Mem()
	return pb.NextDecoder(verScionTmp)
}

// SCMPTraceroute represents the structure of a traceroute.
//
//	 0                   1                   2                   3
//	 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
//	+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//	|           Identifier          |        Sequence Number        |
//	+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//	|              ISD              |                               |
//	+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+         AS                    +
//	|                                                               |
//	+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//	|                                                               |
//	+                        Interface ID                           +
//	|                                                               |
//	+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
type SCMPTraceroute struct {
	BaseLayer

	Identifier uint16
	Sequence   uint16
	IA         addr.IA
	Interface  uint64
}

// LayerType returns LayerTypeSCMPTraceroute.
// @ decreases
// @ pure
func (i *SCMPTraceroute) LayerType() gopacket.LayerType {
	return LayerTypeSCMPTraceroute
}

// NextLayerType returns the layer type contained by this DecodingLayer.
// @ decreases
// @ pure
func (*SCMPTraceroute) NextLayerType() gopacket.LayerType {
	return gopacket.LayerTypePayload
}

// DecodeFromBytes decodes the given bytes into this layer.
// @ requires  df != nil
// @ requires  i.NonInitMem()
// @ preserves acc(sl.Bytes(data, 0, len(data)), R40)
// @ preserves df.Mem()
// @ ensures   res == nil ==> i.Mem(data)
// @ ensures   res != nil ==> i.NonInitMem()
// @ ensures   res != nil ==> res.ErrorMem()
// @ decreases
func (i *SCMPTraceroute) DecodeFromBytes(data []byte, df gopacket.DecodeFeedback) (res error) {
	minLength := 2 + 2 + addr.IABytes + scmpRawInterfaceLen
	if size := len(data); size < minLength {
		df.SetTruncated()
		return serrors.New("buffer too short", "min", minLength, "actual", size)
	}
	// @ unfold i.NonInitMem()
	// @ defer fold i.Mem(data)
	offset := 0
	// the reads only need element permissions, so the buffer is unfolded once
	// @ unfold acc(sl.Bytes(data, 0, len(data)), R40)
	// @ assert &data[offset : offset+2][0] == &data[offset]
	// @ assert &data[offset : offset+2][1] == &data[offset+1]
	i.Identifier = binary.BigEndian.Uint16(data[offset : offset+2])
	offset += 2
	// @ assert &data[offset : offset+2][0] == &data[offset]
	// @ assert &data[offset : offset+2][1] == &data[offset+1]
	i.Sequence = binary.BigEndian.Uint16(data[offset : offset+2])
	offset += 2
	// @ sl.AssertSliceOverlap(data, offset, offset+addr.IABytes)
	i.IA = addr.IA(binary.BigEndian.Uint64(data[offset : offset+addr.IABytes]))
	offset += addr.IABytes
	// @ sl.AssertSliceOverlap(data, offset, offset+scmpRawInterfaceLen)
	i.Interface = binary.BigEndian.Uint64(data[offset : offset+scmpRawInterfaceLen])
	// @ fold acc(sl.Bytes(data, 0, len(data)), R40)
	offset += scmpRawInterfaceLen
	i.BaseLayer = BaseLayer{
		Contents: data[:offset],
		Payload:  data[offset:],
	}
	// @ fold i.BaseLayer.Mem(data, 4+addr.IABytes+scmpRawInterfaceLen)
	return nil
}

// SerializeTo writes the serialized form of this layer into the
// SerializationBuffer, implementing gopacket.SerializableLayer.
// @ requires  b != nil
// @ requires  i.Mem(ubufMem)
// @ preserves b.Mem()
// @ preserves sl.Bytes(b.UBuf(), 0, len(b.UBuf()))
// @ ensures   err == nil ==> i.Mem(ubufMem)
// @ ensures   err != nil ==> err.ErrorMem()
// @ decreases
func (i *SCMPTraceroute) SerializeTo(b gopacket.SerializeBuffer, opts gopacket.SerializeOptions /*@, ghost ubufMem []byte @*/) (err error) {

	buf, err := b.PrependBytes(2 + 2 + addr.IABytes + scmpRawInterfaceLen)
	//@ ghost underlyingBufRes := b.UBuf()
	if err != nil {
		return err
	}
	offset := 0
	// @ unfold i.Mem(ubufMem)
	// @ defer fold i.Mem(ubufMem)
	// @ assert buf === underlyingBufRes[:2+2+addr.IABytes+scmpRawInterfaceLen]
	// the writes only need element permissions, so the buffer is unfolded once
	// @ unfold sl.Bytes(underlyingBufRes, 0, len(underlyingBufRes))
	// @ assert forall k int :: { &buf[k] } { &underlyingBufRes[k] } 0 <= k && k < len(buf) ==> &buf[k] == &underlyingBufRes[k]
	// @ assert &buf[:2][0] == &buf[0] && &buf[:2][1] == &buf[1]
	binary.BigEndian.PutUint16(buf[:2], i.Identifier)
	offset += 2
	// @ assert &buf[offset : offset+2][0] == &buf[offset]
	// @ assert &buf[offset : offset+2][1] == &buf[offset+1]
	binary.BigEndian.PutUint16(buf[offset:offset+2], i.Sequence)
	offset += 2
	// @ sl.AssertSliceOverlap(buf, offset, offset+addr.IABytes)
	binary.BigEndian.PutUint64(buf[offset:offset+addr.IABytes], uint64(i.IA))
	offset += addr.IABytes
	// @ sl.AssertSliceOverlap(buf, offset, offset+scmpRawInterfaceLen)
	binary.BigEndian.PutUint64(buf[offset:offset+scmpRawInterfaceLen], i.Interface)
	// @ fold sl.Bytes(underlyingBufRes, 0, len(underlyingBufRes))
	return nil
}

// @ requires  pb != nil
// @ preserves pb.Mem()
// @ requires  sl.Bytes(data, 0, len(data))
// @ ensures   err != nil ==> err.ErrorMem()
// @ decreases
func decodeSCMPTraceroute(data []byte, pb gopacket.PacketBuilder) (err error) {
	s := &SCMPTraceroute{}
	// @ fold s.NonInitMem()
	if err := s.DecodeFromBytes(data, pb); err != nil {
		return err
	}
	pb.AddLayer(s)
	verScionTmp := s.NextLayerType()
	// @ fold verScionTmp.Mem()
	return pb.NextDecoder(verScionTmp)
}

// SCMPDestinationUnreachable represents the structure of a destination
// unreachable message.
//
//	 0                   1                   2                   3
//	 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
//	+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//	|                             Unused                            |
//	+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
type SCMPDestinationUnreachable struct {
	BaseLayer
}

// LayerType returns LayerTypeSCMPTraceroute.
// @ decreases
// @ pure
func (i *SCMPDestinationUnreachable) LayerType() gopacket.LayerType {
	return LayerTypeSCMPDestinationUnreachable
}

// NextLayerType returns the layer type contained by this DecodingLayer.
// @ decreases
// @ pure
func (*SCMPDestinationUnreachable) NextLayerType() gopacket.LayerType {
	return gopacket.LayerTypePayload
}

// DecodeFromBytes decodes the given bytes into this layer.
// @ requires  df != nil
// @ requires  i.NonInitMem()
// @ requires  sl.Bytes(data, 0, len(data))
// @ preserves df.Mem()
// @ ensures   res == nil ==> i.Mem(data)
// @ ensures   res != nil ==> (i.NonInitMem() && sl.Bytes(data, 0, len(data)))
// @ ensures   res != nil ==> res.ErrorMem()
// @ decreases
func (i *SCMPDestinationUnreachable) DecodeFromBytes(data []byte,
	df gopacket.DecodeFeedback) (res error) {

	minLength := 4
	if size := len(data); size < minLength {
		df.SetTruncated()
		return serrors.New("buffer too short", "min", minLength, "actual", size)
	}
	// @ unfold i.NonInitMem()
	// @ defer fold i.Mem(data)
	// @ defer fold i.BaseLayer.Mem(data, minLength)
	// @ unfold sl.Bytes(data, 0, len(data))
	// @ sl.AssertSliceOverlap(data, minLength, len(data))
	i.BaseLayer = BaseLayer{
		Contents: data[:minLength],
		Payload:  data[minLength:],
	}
	// @ assert forall l int :: { &i.Payload[l] } 0 <= l && l < len(i.Payload) ==>
	// @ 	&data[minLength:][l] == &i.Payload[l]
	// @ fold sl.Bytes(i.Contents, 0, len(i.Contents))
	// @ fold sl.Bytes(i.Payload, 0, len(i.Payload))
	return nil
}

// SerializeTo writes the serialized form of this layer into the
// SerializationBuffer, implementing gopacket.SerializableLayer.
// @ requires  b != nil
// @ requires  i.Mem(ubufMem)
// @ preserves b.Mem()
// @ preserves sl.Bytes(b.UBuf(), 0, len(b.UBuf()))
// @ ensures   err == nil ==> i.Mem(ubufMem)
// @ ensures   err != nil ==> err.ErrorMem()
// @ decreases
func (i *SCMPDestinationUnreachable) SerializeTo(b gopacket.SerializeBuffer, opts gopacket.SerializeOptions /*@, ghost ubufMem []byte @*/) (err error) {

	buf, err := b.PrependBytes(4)
	// @ ghost underlyingBufRes := b.UBuf()
	if err != nil {
		return err
	}
	// @ assert buf === underlyingBufRes[:4]
	// the copy only needs element permissions, so the buffer is unfolded once
	// @ unfold sl.Bytes(underlyingBufRes, 0, len(underlyingBufRes))
	// @ assert forall k int :: { &buf[k] } { &underlyingBufRes[k] } 0 <= k && k < len(buf) ==> &buf[k] == &underlyingBufRes[k]
	copy(buf, make([]byte, 4) /*@, writePerm@*/)
	// @ fold sl.Bytes(underlyingBufRes, 0, len(underlyingBufRes))
	return nil
}

// @ requires  pb != nil
// @ requires  sl.Bytes(data, 0, len(data))
// @ preserves pb.Mem()
// @ ensures   err != nil ==> err.ErrorMem()
// @ decreases
func decodeSCMPDestinationUnreachable(data []byte, pb gopacket.PacketBuilder) (err error) {
	s := &SCMPDestinationUnreachable{}
	// @ fold s.NonInitMem()
	if err := s.DecodeFromBytes(data, pb); err != nil {
		return err
	}
	pb.AddLayer(s)
	verScionTmp := s.NextLayerType()
	// @ fold verScionTmp.Mem()
	return pb.NextDecoder(verScionTmp)
}

// SCMPPacketTooBig represents the structure of a packet too big message.
//
//	+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//	|            reserved           |             MTU               |
//	+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
type SCMPPacketTooBig struct {
	BaseLayer

	MTU uint16
}

// LayerType returns LayerTypeSCMPParameterProblem.
// @ decreases
// @ pure
func (i *SCMPPacketTooBig) LayerType() gopacket.LayerType {
	return LayerTypeSCMPPacketTooBig
}

// NextLayerType returns the layer type contained by this DecodingLayer.
// @ decreases
// @ pure
func (*SCMPPacketTooBig) NextLayerType() gopacket.LayerType {
	return gopacket.LayerTypePayload
}

// DecodeFromBytes decodes the given bytes into this layer.
// @ requires  df != nil
// @ requires  sl.Bytes(data, 0, len(data))
// @ requires  i.NonInitMem()
// @ preserves df.Mem()
// @ ensures   res == nil ==> i.Mem(data)
// @ ensures   res != nil ==> (i.NonInitMem() && sl.Bytes(data, 0, len(data)))
// @ ensures   res != nil ==> res.ErrorMem()
// @ decreases
func (i *SCMPPacketTooBig) DecodeFromBytes(data []byte, df gopacket.DecodeFeedback) (res error) {
	minLength := 2 + 2
	if size := len(data); size < minLength {
		df.SetTruncated()
		return serrors.New("buffer too short", "min", minLength, "actual", size)
	}
	// @ unfold i.NonInitMem()
	// @ defer fold i.Mem(data)
	// the read only needs element permissions, so the buffer is unfolded once
	// @ unfold sl.Bytes(data, 0, len(data))
	// @ assert &data[2:4][0] == &data[2]
	// @ assert &data[2:4][1] == &data[3]
	i.MTU = binary.BigEndian.Uint16(data[2:4])
	// @ fold sl.Bytes(data, 0, len(data))
	i.BaseLayer = BaseLayer{
		Contents: data[:4],
		Payload:  data[4:],
	}
	// @ fold i.BaseLayer.Mem(data, 4)
	return nil
}

// SerializeTo writes the serialized form of this layer into the
// SerializationBuffer, implementing gopacket.SerializableLayer.
// @ requires  b != nil
// @ requires  i.Mem(ubufMem)
// @ preserves b.Mem()
// @ preserves sl.Bytes(b.UBuf(), 0, len(b.UBuf()))
// @ ensures   err == nil ==> i.Mem(ubufMem)
// @ ensures   err != nil ==> err.ErrorMem()
// @ decreases
func (i *SCMPPacketTooBig) SerializeTo(b gopacket.SerializeBuffer, opts gopacket.SerializeOptions /*@, ghost ubufMem []byte @*/) (err error) {

	buf, err := b.PrependBytes(2 + 2)
	// @ ghost underlyingBufRes := b.UBuf()
	if err != nil {
		return err
	}
	// @ unfold i.Mem(ubufMem)
	// @ defer fold i.Mem(ubufMem)
	// @ assert buf === underlyingBufRes[:2+2]
	// the writes only need element permissions, so the buffer is unfolded once
	// @ unfold sl.Bytes(underlyingBufRes, 0, len(underlyingBufRes))
	// @ assert forall k int :: { &buf[k] } { &underlyingBufRes[k] } 0 <= k && k < len(buf) ==> &buf[k] == &underlyingBufRes[k]
	// @ assert &buf[0:2][0] == &buf[0] && &buf[0:2][1] == &buf[1]
	binary.BigEndian.PutUint16(buf[0:2], uint16(0)) //Reserved
	// @ assert &buf[2:4][0] == &buf[2]
	// @ assert &buf[2:4][1] == &buf[3]
	binary.BigEndian.PutUint16(buf[2:4], i.MTU)
	// @ fold sl.Bytes(underlyingBufRes, 0, len(underlyingBufRes))
	return nil
}

// @ requires  pb != nil
// @ preserves pb.Mem()
// @ requires  sl.Bytes(data, 0, len(data))
// @ ensures   err != nil ==> err.ErrorMem()
// @ decreases
func decodeSCMPPacketTooBig(data []byte, pb gopacket.PacketBuilder) (err error) {
	s := &SCMPPacketTooBig{}
	// @ fold s.NonInitMem()
	if err := s.DecodeFromBytes(data, pb); err != nil {
		return err
	}
	pb.AddLayer(s)
	verScionTmp := s.NextLayerType()
	// @ fold verScionTmp.Mem()
	return pb.NextDecoder(verScionTmp)
}
