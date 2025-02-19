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
// @ requires  0 <= 0 && 0 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < len(data) ==> acc(&data[i])
// @ preserves df.Mem()
// @ ensures   res == nil ==> i.Mem(data)
// @ ensures   res != nil ==> (i.NonInitMem() && 0 <= 0 && 0 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < len(data) ==> acc(&data[i]))
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
	// @ sl.SplitRange_Bytes(data, offset, len(data), R15)

	i.IA = addr.IA(binary.BigEndian.Uint64(data[offset:]))

	// @ sl.CombineRange_Bytes(data, offset, len(data), R15)
	offset += addr.IABytes
	// @ sl.SplitRange_Bytes(data, offset, offset+scmpRawInterfaceLen, R15)
	// @ ghost newSlice := data[offset : offset+scmpRawInterfaceLen]

	i.IfID = binary.BigEndian.Uint64(data[offset : offset+scmpRawInterfaceLen])

	// @ sl.CombineRange_Bytes(data, offset, offset+scmpRawInterfaceLen, R15)
	offset += scmpRawInterfaceLen
	// @ sl.Reslice_Bytes(data, 0, offset, writePerm)
	// @ sl.Reslice_Bytes(data, offset, len(data), writePerm)
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
// @ preserves 0 <= 0 && 0 <= len(b.UBuf()) && len(b.UBuf()) <= cap(b.UBuf()) && forall i int :: { &b.UBuf()[i] } 0 <= i && i < len(b.UBuf()) ==> acc(&b.UBuf()[i])
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
	// @ sl.SplitRange_Bytes(underlyingBufRes, 0, len(buf), writePerm)
	// @ assert 0 <= 0 && 0 <= len(buf) && len(buf) <= cap(buf) && forall i int :: { &buf[i] } 0 <= i && i < len(buf) ==> acc(&buf[i])

	binary.BigEndian.PutUint64(buf[offset:], uint64(i.IA))

	offset += addr.IABytes
	// @ sl.SplitRange_Bytes(buf, offset, offset+scmpRawInterfaceLen, writePerm)
	// @ ghost newSlice := buf[offset:offset+scmpRawInterfaceLen]

	binary.BigEndian.PutUint64(buf[offset:offset+scmpRawInterfaceLen], i.IfID)

	// @ sl.CombineRange_Bytes(buf, offset, offset+scmpRawInterfaceLen, writePerm)
	// @ sl.CombineRange_Bytes(underlyingBufRes, 0, len(buf), writePerm)
	return nil
}

// @ requires pb != nil
// @ preserves pb.Mem()
// @ requires 0 <= 0 && 0 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < len(data) ==> acc(&data[i])
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
// @ requires  0 <= 0 && 0 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < len(data) ==> acc(&data[i])
// @ requires  i.NonInitMem()
// @ preserves df.Mem()
// @ ensures   res == nil ==> i.Mem(data)
// @ ensures   res != nil ==> (i.NonInitMem() && 0 <= 0 && 0 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < len(data) ==> acc(&data[i]))
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
	// @ sl.SplitRange_Bytes(data, offset, len(data), R15)

	i.IA = addr.IA(binary.BigEndian.Uint64(data[offset:]))

	// @ sl.CombineRange_Bytes(data, offset, len(data), R15)
	offset += addr.IABytes
	// @ sl.SplitRange_Bytes(data, offset, offset+scmpRawInterfaceLen, R15)
	// @ ghost newSlice := data[offset : offset+scmpRawInterfaceLen]

	i.Ingress = binary.BigEndian.Uint64(data[offset : offset+scmpRawInterfaceLen])

	// @ sl.CombineRange_Bytes(data, offset, offset+scmpRawInterfaceLen, R15)
	offset += scmpRawInterfaceLen
	// @ sl.SplitRange_Bytes(data, offset, offset+scmpRawInterfaceLen, R15)
	// @ ghost newSlice = data[offset : offset+scmpRawInterfaceLen]

	i.Egress = binary.BigEndian.Uint64(data[offset : offset+scmpRawInterfaceLen])

	// @ sl.CombineRange_Bytes(data, offset, offset+scmpRawInterfaceLen, R15)
	offset += scmpRawInterfaceLen
	// @ sl.Reslice_Bytes(data, 0, offset, writePerm)
	// @ sl.Reslice_Bytes(data, offset, len(data), writePerm)
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
// @ preserves 0 <= 0 && 0 <= len(b.UBuf()) && len(b.UBuf()) <= cap(b.UBuf()) && forall i int :: { &b.UBuf()[i] } 0 <= i && i < len(b.UBuf()) ==> acc(&b.UBuf()[i])
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
	// @ sl.SplitRange_Bytes(underlyingBufRes, 0, len(buf), writePerm)
	// @ assert 0 <= 0 && 0 <= len(buf) && len(buf) <= cap(buf) && forall i int :: { &buf[i] } 0 <= i && i < len(buf) ==> acc(&buf[i])
	// @ sl.SplitRange_Bytes(buf, offset, len(buf), writePerm)

	binary.BigEndian.PutUint64(buf[offset:], uint64(i.IA))

	// @ sl.CombineRange_Bytes(buf, offset, len(buf), writePerm)
	offset += addr.IABytes
	// @ ghost newSlice := buf[offset:offset+scmpRawInterfaceLen]
	// @ sl.SplitRange_Bytes(buf, offset, offset+scmpRawInterfaceLen, writePerm)

	binary.BigEndian.PutUint64(buf[offset:offset+scmpRawInterfaceLen], i.Ingress)

	// @ sl.CombineRange_Bytes(buf, offset, offset+scmpRawInterfaceLen, writePerm)
	offset += scmpRawInterfaceLen
	// @ ghost newSlice = buf[offset:offset+scmpRawInterfaceLen]
	// @ sl.SplitRange_Bytes(buf, offset, offset+scmpRawInterfaceLen, writePerm)

	binary.BigEndian.PutUint64(buf[offset:offset+scmpRawInterfaceLen], i.Egress)

	// @ sl.CombineRange_Bytes(buf, offset, offset+scmpRawInterfaceLen, writePerm)
	// @ sl.CombineRange_Bytes(underlyingBufRes, 0, len(buf), writePerm)
	return nil
}

// @ requires pb != nil
// @ preserves pb.Mem()
// @ requires 0 <= 0 && 0 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < len(data) ==> acc(&data[i])
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
// @ requires  0 <= 0 && 0 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < len(data) ==> acc(&data[i])
// @ preserves df.Mem()
// @ ensures   res == nil ==> i.Mem(data)
// @ ensures   res != nil ==> (i.NonInitMem() && 0 <= 0 && 0 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < len(data) ==> acc(&data[i]))
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
	// @ requires offset == 0
	// @ preserves acc(&i.Identifier)
	// @ requires len(data) >= 4
	// @ requires 0 <= 0 && 0 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < len(data) ==> acc(&data[i])
	// @ ensures 0 <= 2 && 2 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 2 <= i && i < len(data) ==> acc(&data[i])
	// @ ensures 0 <= 0 && 0 <= 2 && 2 <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < 2 ==> acc(&data[i])
	// @ decreases
	// @ outline (

	i.Identifier = binary.BigEndian.Uint16(data[:2])

	// @ )
	offset += 2
	// @ requires offset == 2
	// @ preserves acc(&i.SeqNumber)
	// @ requires len(data) >= 4
	// @ requires 0 <= 2 && 2 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 2 <= i && i < len(data) ==> acc(&data[i])
	// @ ensures 0 <= 2 && 2 <= 4 && 4 <= cap(data) && forall i int :: { &data[i] } 2 <= i && i < 4 ==> acc(&data[i])
	// @ ensures 0 <= 4 && 4 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 4 <= i && i < len(data) ==> acc(&data[i])
	// @ decreases
	// @ outline (

	// @ assert &data[offset : offset+2][0] == &data[offset]
	// @ assert &data[offset : offset+2][1] == &data[offset+1]
	i.SeqNumber = binary.BigEndian.Uint16(data[offset : offset+2])

	// @ )
	offset += 2
	// @ requires offset == 4
	// @ requires len(data) >= 4
	// @ requires acc(&i.BaseLayer)
	// @ requires 0 <= 0 && 0 <= 2 && 2 <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < 2 ==> acc(&data[i])
	// @ requires 0 <= 2 && 2 <= 4 && 4 <= cap(data) && forall i int :: { &data[i] } 2 <= i && i < 4 ==> acc(&data[i])
	// @ requires 0 <= 4 && 4 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 4 <= i && i < len(data) ==> acc(&data[i])
	// @ ensures  acc(i.BaseLayer.Mem(data, 4))
	// @ decreases
	// @ outline (


	// @ sl.AssertSliceOverlap(data, offset, len(data))
	i.BaseLayer = BaseLayer{
		Contents: data[:offset],
		Payload:  data[offset:],
	}
	// @ assert forall l int :: { &i.Payload[l] } 0 <= l && l < len(i.Payload) ==>
	// @ 	&data[offset+l] == &i.Payload[l]
	// @ assert forall l int :: { &i.Payload[l] } 0 <= l && l < len(i.Payload) ==>
	// @ 	acc(&i.Payload[l])


	// @ fold i.BaseLayer.Mem(data, 4)
	// @ )
	return nil
}

// SerializeTo writes the serialized form of this layer into the
// SerializationBuffer, implementing gopacket.SerializableLayer.
// @ requires  b != nil
// @ requires  i.Mem(ubufMem)
// @ preserves b.Mem()
// @ preserves 0 <= 0 && 0 <= len(b.UBuf()) && len(b.UBuf()) <= cap(b.UBuf()) && forall i int :: { &b.UBuf()[i] } 0 <= i && i < len(b.UBuf()) ==> acc(&b.UBuf()[i])
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

	binary.BigEndian.PutUint16(buf[:2], i.Identifier)

	offset += 2

	// @ assert &buf[offset : offset+2][0] == &buf[offset]
	// @ assert &buf[offset : offset+2][1] == &buf[offset+1]
	binary.BigEndian.PutUint16(buf[offset:offset+2], i.SeqNumber)

	return nil
}

// @ requires pb != nil
// @ preserves pb.Mem()
// @ requires 0 <= 0 && 0 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < len(data) ==> acc(&data[i])
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
// @ requires  0 <= 0 && 0 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < len(data) ==> acc(&data[i])
// @ preserves df.Mem()
// @ ensures   res == nil ==> i.Mem(data)
// @ ensures   res != nil ==> (i.NonInitMem() && 0 <= 0 && 0 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < len(data) ==> acc(&data[i]))
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
	// @ preserves acc(&i.Pointer)
	// @ requires len(data) >= 4
	// @ preserves 0 <= 0 && 0 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < len(data) ==> acc(&data[i])
	// @ decreases
	// @ outline (

	// @ assert &data[2:4][0] == &data[2]
	// @ assert &data[2:4][1] == &data[3]
	i.Pointer = binary.BigEndian.Uint16(data[2:4])

	// @ )
	// @ requires len(data) >= 4
	// @ requires acc(&i.BaseLayer)
	// @ ensures  i.BaseLayer.Mem(data, 4)
	// @ requires 0 <= 0 && 0 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < len(data) ==> acc(&data[i])
	// @ decreases
	// @ outline (

	// @ sl.AssertSliceOverlap(data, 4, len(data))
	i.BaseLayer = BaseLayer{
		Contents: data[:4],
		Payload:  data[4:],
	}
	// @ assert forall l int :: { &i.Payload[l] } 0 <= l && l < len(i.Payload) ==>
	// @ 	&data[4+l] == &i.Payload[l]


	// @ fold i.BaseLayer.Mem(data, 4)
	// @ )
	return nil
}

// SerializeTo writes the serialized form of this layer into the
// SerializationBuffer, implementing gopacket.SerializableLayer.
// @ requires  b != nil
// @ requires  i.Mem(ubufMem)
// @ preserves b.Mem()
// @ preserves 0 <= 0 && 0 <= len(b.UBuf()) && len(b.UBuf()) <= cap(b.UBuf()) && forall i int :: { &b.UBuf()[i] } 0 <= i && i < len(b.UBuf()) ==> acc(&b.UBuf()[i])
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

	binary.BigEndian.PutUint16(buf[0:2], uint16(0)) //Reserved


	// @ assert &buf[2:4][0] == &buf[2]
	// @ assert &buf[2:4][1] == &buf[3]
	binary.BigEndian.PutUint16(buf[2:4], i.Pointer)

	return nil
}

// @ requires  pb != nil
// @ preserves pb.Mem()
// @ requires  0 <= 0 && 0 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < len(data) ==> acc(&data[i])
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
// @ preserves 0 <= 0 && 0 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < len(data) ==> acc(&data[i], R40)
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
	// @ requires offset == 0
	// @ preserves acc(&i.Identifier)
	// @ requires len(data) >= 2 + 2 + addr.IABytes + scmpRawInterfaceLen
	// @ requires  0 <= 0 && 0 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < len(data) ==> acc(&data[i], R40)
	// @ ensures   0 <= 0 && 0 <= 2 && 2 <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < 2 ==> acc(&data[i], R40)
	// @ ensures   0 <= 2 && 2 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 2 <= i && i < len(data) ==> acc(&data[i], R40)
	// @ decreases
	// @ outline (

	i.Identifier = binary.BigEndian.Uint16(data[offset : offset+2])

	// @ )
	offset += 2
	// @ requires offset == 2
	// @ preserves acc(&i.Sequence)
	// @ requires len(data) >= 2 + 2 + addr.IABytes + scmpRawInterfaceLen
	// @ requires 0 <= 2 && 2 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 2 <= i && i < len(data) ==> acc(&data[i], R40)
	// @ ensures 0 <= 2 && 2 <= 2+2 && 2+2 <= cap(data) && forall i int :: { &data[i] } 2 <= i && i < 2+2 ==> acc(&data[i], R40)
	// @ ensures 0 <= 2+2 && 2+2 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 2+2 <= i && i < len(data) ==> acc(&data[i], R40)
	// @ decreases
	// @ outline (

	// @ assert &data[offset : offset+2][0] == &data[offset]
	// @ assert &data[offset : offset+2][1] == &data[offset+1]
	i.Sequence = binary.BigEndian.Uint16(data[offset : offset+2])

	// @ )
	offset += 2
	// @ requires offset == 2 + 2
	// @ preserves acc(&i.IA)
	// @ requires len(data) >= 2 + 2 + addr.IABytes + scmpRawInterfaceLen
	// @ requires 0 <= 2+2 && 2+2 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 2+2 <= i && i < len(data) ==> acc(&data[i], R40)
	// @ ensures 0 <= 2+2 && 2+2 <= 2+2+addr.IABytes && 2+2+addr.IABytes <= cap(data) && forall i int :: { &data[i] } 2+2 <= i && i < 2+2+addr.IABytes ==> acc(&data[i], R40)
	// @ ensures 0 <= 2+2+addr.IABytes && 2+2+addr.IABytes <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 2+2+addr.IABytes <= i && i < len(data) ==> acc(&data[i], R40)
	// @ decreases
	// @ outline (

	// @ sl.AssertSliceOverlap(data, offset, offset+addr.IABytes)
	i.IA = addr.IA(binary.BigEndian.Uint64(data[offset : offset+addr.IABytes]))

	// @ )
	offset += addr.IABytes
	// @ requires offset == 2 + 2 + addr.IABytes
	// @ preserves acc(&i.Interface)
	// @ requires len(data) >= 2 + 2 + addr.IABytes + scmpRawInterfaceLen
	// @ requires  0 <= 2+2+addr.IABytes && 2+2+addr.IABytes <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 2+2+addr.IABytes <= i && i < len(data) ==> acc(&data[i], R40)
	// @ ensures  0 <= 2+2+addr.IABytes && 2+2+addr.IABytes <= 2+2+addr.IABytes+scmpRawInterfaceLen && 2+2+addr.IABytes+scmpRawInterfaceLen <= cap(data) && forall i int :: { &data[i] } 2+2+addr.IABytes <= i && i < 2+2+addr.IABytes+scmpRawInterfaceLen ==> acc(&data[i], R40)
	// @ ensures  0 <= 2+2+addr.IABytes+scmpRawInterfaceLen && 2+2+addr.IABytes+scmpRawInterfaceLen <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 2+2+addr.IABytes+scmpRawInterfaceLen <= i && i < len(data) ==> acc(&data[i], R40)
	// @ decreases
	// @ outline (

	// @ sl.AssertSliceOverlap(data, offset, offset+scmpRawInterfaceLen)
	i.Interface = binary.BigEndian.Uint64(data[offset : offset+scmpRawInterfaceLen])

	// @ )
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
// @ preserves 0 <= 0 && 0 <= len(b.UBuf()) && len(b.UBuf()) <= cap(b.UBuf()) && forall i int :: { &b.UBuf()[i] } 0 <= i && i < len(b.UBuf()) ==> acc(&b.UBuf()[i])
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

	return nil
}

// @ requires  pb != nil
// @ preserves pb.Mem()
// @ requires  0 <= 0 && 0 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < len(data) ==> acc(&data[i])
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
// @ requires  0 <= 0 && 0 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < len(data) ==> acc(&data[i])
// @ preserves df.Mem()
// @ ensures   res == nil ==> i.Mem(data)
// @ ensures   res != nil ==> (i.NonInitMem() && 0 <= 0 && 0 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < len(data) ==> acc(&data[i]))
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

	// @ sl.AssertSliceOverlap(data, minLength, len(data))
	i.BaseLayer = BaseLayer{
		Contents: data[:minLength],
		Payload:  data[minLength:],
	}
	// @ assert forall l int :: { &i.Payload[l] } 0 <= l && l < len(i.Payload) ==>
	// @ 	&data[minLength:][l] == &i.Payload[l]


	return nil
}

// SerializeTo writes the serialized form of this layer into the
// SerializationBuffer, implementing gopacket.SerializableLayer.
// @ requires  b != nil
// @ requires  i.Mem(ubufMem)
// @ preserves b.Mem()
// @ preserves 0 <= 0 && 0 <= len(b.UBuf()) && len(b.UBuf()) <= cap(b.UBuf()) && forall i int :: { &b.UBuf()[i] } 0 <= i && i < len(b.UBuf()) ==> acc(&b.UBuf()[i])
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

	copy(buf, make([]byte, 4) /*@, writePerm@*/)

	return nil
}

// @ requires  pb != nil
// @ requires  0 <= 0 && 0 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < len(data) ==> acc(&data[i])
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
// @ requires  0 <= 0 && 0 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < len(data) ==> acc(&data[i])
// @ requires  i.NonInitMem()
// @ preserves df.Mem()
// @ ensures   res == nil ==> i.Mem(data)
// @ ensures   res != nil ==> (i.NonInitMem() && 0 <= 0 && 0 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < len(data) ==> acc(&data[i]))
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
	// @ preserves acc(&i.MTU)
	// @ requires len(data) >= 4
	// @ preserves 0 <= 0 && 0 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < len(data) ==> acc(&data[i])
	// @ decreases
	// @ outline (

	// @ assert &data[2:4][0] == &data[2]
	// @ assert &data[2:4][1] == &data[3]
	i.MTU = binary.BigEndian.Uint16(data[2:4])

	// @ )
	// @ requires len(data) >= 4
	// @ requires acc(&i.BaseLayer)
	// @ requires 0 <= 0 && 0 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < len(data) ==> acc(&data[i])
	// @ ensures  i.BaseLayer.Mem(data, 4)
	// @ decreases
	// @ outline (

	// @ sl.AssertSliceOverlap(data, 4, len(data))
	i.BaseLayer = BaseLayer{
		Contents: data[:4],
		Payload:  data[4:],
	}
	// @ assert forall l int :: { &i.Payload[l] } 0 <= l && l < len(i.Payload) ==>
	// @ 	&data[4+l] == &i.Payload[l]


	// @ fold i.BaseLayer.Mem(data, 4)
	// @ )
	return nil
}

// SerializeTo writes the serialized form of this layer into the
// SerializationBuffer, implementing gopacket.SerializableLayer.
// @ requires  b != nil
// @ requires  i.Mem(ubufMem)
// @ preserves b.Mem()
// @ preserves 0 <= 0 && 0 <= len(b.UBuf()) && len(b.UBuf()) <= cap(b.UBuf()) && forall i int :: { &b.UBuf()[i] } 0 <= i && i < len(b.UBuf()) ==> acc(&b.UBuf()[i])
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

	binary.BigEndian.PutUint16(buf[0:2], uint16(0)) //Reserved


	// @ assert &buf[2:4][0] == &buf[2]
	// @ assert &buf[2:4][1] == &buf[3]
	binary.BigEndian.PutUint16(buf[2:4], i.MTU)

	return nil
}

// @ requires  pb != nil
// @ preserves pb.Mem()
// @ requires  0 <= 0 && 0 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < len(data) ==> acc(&data[i])
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
