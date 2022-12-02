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
	// @ def "github.com/scionproto/scion/verification/utils/definitions"
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
// @ requires  sl.AbsSlice_Bytes(data, 0, len(data))
// @ preserves df.Mem()
// @ ensures   res == nil ==> i.Mem(data)
// @ ensures   res != nil ==> (i.NonInitMem() && sl.AbsSlice_Bytes(data, 0, len(data)))
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
	// @ sl.SplitRange_Bytes(data, offset, len(data), def.ReadL15)
	// @ unfold acc(sl.AbsSlice_Bytes(data[offset:], 0, len(data[offset:])), def.ReadL15)
	i.IA = addr.IA(binary.BigEndian.Uint64(data[offset:]))
	// @ fold acc(sl.AbsSlice_Bytes(data[offset:], 0, len(data[offset:])), def.ReadL15)
	// @ sl.CombineRange_Bytes(data, offset, len(data), def.ReadL15)
	offset += addr.IABytes
	// @ sl.SplitRange_Bytes(data, offset, offset+scmpRawInterfaceLen, def.ReadL15)
	// @ ghost newSlice := data[offset : offset+scmpRawInterfaceLen]
	// @ unfold acc(sl.AbsSlice_Bytes(newSlice, 0, len(newSlice)), def.ReadL15)
	i.IfID = binary.BigEndian.Uint64(data[offset : offset+scmpRawInterfaceLen])
	// @ fold acc(sl.AbsSlice_Bytes(newSlice, 0, len(newSlice)), def.ReadL15)
	// @ sl.CombineRange_Bytes(data, offset, offset+scmpRawInterfaceLen, def.ReadL15)
	offset += scmpRawInterfaceLen
	// @ sl.SplitByIndex_Bytes(data, 0, len(data), offset, writePerm)
	// @ sl.Reslice_Bytes(data, 0, offset, writePerm)
	// @ sl.Reslice_Bytes(data, offset, len(data), writePerm)
	i.BaseLayer = BaseLayer{
		Contents: data[:offset],
		Payload:  data[offset:],
	}
	// @ fold i.BaseLayer.Mem(data)
	// @ fold i.Mem(data)
	return nil
}

// SerializeTo writes the serialized form of this layer into the
// SerializationBuffer, implementing gopacket.SerializableLayer.
// @ requires b != nil
// @ requires i.Mem(ubufMem)
// @ requires b.Mem(underlyingBuf)
// @ ensures  err == nil ==> underlyingBufRes != nil
// @ ensures  err == nil ==> i.Mem(ubufMem) && b.Mem(underlyingBufRes)
// @ ensures  err != nil ==> b.Mem(underlyingBuf)
// @ ensures  err != nil ==> err.ErrorMem()
// @ decreases
func (i *SCMPExternalInterfaceDown) SerializeTo(b gopacket.SerializeBuffer, opts gopacket.SerializeOptions /*@, ghost ubufMem []byte, ghost underlyingBuf []byte @*/) (err error /*@, ghost underlyingBufRes []byte @*/) {

	buf, err /*@, underlyingBufRes@*/ := b.PrependBytes(addr.IABytes + scmpRawInterfaceLen /*@, underlyingBuf@*/)
	if err != nil {
		return err /*@, underlyingBufRes @*/
	}
	offset := 0
	// @ unfold i.Mem(ubufMem)
	// @ defer fold i.Mem(ubufMem)
	// @ b.ExchangePred(underlyingBufRes)
	// @ assert buf === underlyingBufRes[:addr.IABytes+scmpRawInterfaceLen]
	// @ sl.SplitRange_Bytes(underlyingBufRes, 0, len(buf), writePerm)
	// @ assert sl.AbsSlice_Bytes(buf, 0, len(buf))
	// @ unfold sl.AbsSlice_Bytes(buf, 0, len(buf))
	binary.BigEndian.PutUint64(buf[offset:], uint64(i.IA))
	// @ fold sl.AbsSlice_Bytes(buf, 0, len(buf))
	offset += addr.IABytes
	// @ sl.SplitRange_Bytes(buf, offset, offset+scmpRawInterfaceLen, writePerm)
	// @ ghost newSlice := buf[offset:offset+scmpRawInterfaceLen]
	// @ unfold sl.AbsSlice_Bytes(newSlice, 0, len(newSlice))
	binary.BigEndian.PutUint64(buf[offset:offset+scmpRawInterfaceLen], i.IfID)
	// @ fold sl.AbsSlice_Bytes(newSlice, 0, len(newSlice))
	// @ sl.CombineRange_Bytes(buf, offset, offset+scmpRawInterfaceLen, writePerm)
	// @ sl.CombineRange_Bytes(underlyingBufRes, 0, len(buf), writePerm)
	// @ apply sl.AbsSlice_Bytes(underlyingBufRes, 0, len(underlyingBufRes)) --* b.Mem(underlyingBufRes)
	return nil /*@, underlyingBufRes@*/
}

// @ requires pb != nil
// @ preserves pb.Mem()
// @ requires sl.AbsSlice_Bytes(data, 0, len(data))
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
// @ requires  sl.AbsSlice_Bytes(data, 0, len(data))
// @ requires  i.NonInitMem()
// @ preserves df.Mem()
// @ ensures   res == nil ==> i.Mem(data)
// @ ensures   res != nil ==> (i.NonInitMem() && sl.AbsSlice_Bytes(data, 0, len(data)))
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
	// @ sl.SplitRange_Bytes(data, offset, len(data), def.ReadL15)
	// @ unfold acc(sl.AbsSlice_Bytes(data[offset:], 0, len(data[offset:])), def.ReadL15)
	i.IA = addr.IA(binary.BigEndian.Uint64(data[offset:]))
	// @ fold acc(sl.AbsSlice_Bytes(data[offset:], 0, len(data[offset:])), def.ReadL15)
	// @ sl.CombineRange_Bytes(data, offset, len(data), def.ReadL15)
	offset += addr.IABytes
	// @ sl.SplitRange_Bytes(data, offset, offset+scmpRawInterfaceLen, def.ReadL15)
	// @ ghost newSlice := data[offset : offset+scmpRawInterfaceLen]
	// @ unfold acc(sl.AbsSlice_Bytes(newSlice, 0, len(newSlice)), def.ReadL15)
	i.Ingress = binary.BigEndian.Uint64(data[offset : offset+scmpRawInterfaceLen])
	// @ fold acc(sl.AbsSlice_Bytes(newSlice, 0, len(newSlice)), def.ReadL15)
	// @ sl.CombineRange_Bytes(data, offset, offset+scmpRawInterfaceLen, def.ReadL15)
	offset += scmpRawInterfaceLen
	// @ sl.SplitRange_Bytes(data, offset, offset+scmpRawInterfaceLen, def.ReadL15)
	// @ ghost newSlice = data[offset : offset+scmpRawInterfaceLen]
	// @ unfold acc(sl.AbsSlice_Bytes(newSlice, 0, len(newSlice)), def.ReadL15)
	i.Egress = binary.BigEndian.Uint64(data[offset : offset+scmpRawInterfaceLen])
	// @ fold acc(sl.AbsSlice_Bytes(newSlice, 0, len(newSlice)), def.ReadL15)
	// @ sl.CombineRange_Bytes(data, offset, offset+scmpRawInterfaceLen, def.ReadL15)
	offset += scmpRawInterfaceLen
	// @ sl.SplitByIndex_Bytes(data, 0, len(data), offset, writePerm)
	// @ sl.Reslice_Bytes(data, 0, offset, writePerm)
	// @ sl.Reslice_Bytes(data, offset, len(data), writePerm)
	i.BaseLayer = BaseLayer{
		Contents: data[:offset],
		Payload:  data[offset:],
	}
	// @ fold i.BaseLayer.Mem(data)
	return nil
}

// SerializeTo writes the serialized form of this layer into the
// SerializationBuffer, implementing gopacket.SerializableLayer.
// @ requires b != nil
// @ requires i.Mem(ubufMem)
// @ requires b.Mem(underlyingBuf)
// @ ensures err == nil ==> underlyingBufRes != nil
// @ ensures err == nil ==> i.Mem(ubufMem) && b.Mem(underlyingBufRes)
// @ ensures err != nil ==> b.Mem(underlyingBuf)
// @ ensures err != nil ==> err.ErrorMem()
// @ decreases
func (i *SCMPInternalConnectivityDown) SerializeTo(b gopacket.SerializeBuffer, opts gopacket.SerializeOptions /*@, ghost ubufMem []byte, ghost underlyingBuf []byte @*/) (err error /*@, ghost underlyingBufRes []byte @*/) {

	buf, err /*@, underlyingBufRes@*/ := b.PrependBytes(addr.IABytes + 2*scmpRawInterfaceLen /*@, underlyingBuf@*/)
	if err != nil {
		return err /*@, underlyingBufRes@*/
	}
	offset := 0
	// @ unfold i.Mem(ubufMem)
	// @ defer fold i.Mem(ubufMem)
	// @ b.ExchangePred(underlyingBufRes)
	// @ sl.SplitRange_Bytes(underlyingBufRes, 0, len(buf), writePerm)
	// @ assert sl.AbsSlice_Bytes(buf, 0, len(buf))
	// @ sl.SplitRange_Bytes(buf, offset, len(buf), writePerm)
	// @ unfold sl.AbsSlice_Bytes(buf[offset:], 0, len(buf[offset:]))
	binary.BigEndian.PutUint64(buf[offset:], uint64(i.IA))
	// @ fold sl.AbsSlice_Bytes(buf[offset:], 0, len(buf[offset:]))
	// @ sl.CombineRange_Bytes(buf, offset, len(buf), writePerm)
	offset += addr.IABytes
	// @ ghost newSlice := buf[offset:offset+scmpRawInterfaceLen]
	// @ sl.SplitRange_Bytes(buf, offset, offset+scmpRawInterfaceLen, writePerm)
	// @ unfold sl.AbsSlice_Bytes(newSlice, 0, len(newSlice))
	binary.BigEndian.PutUint64(buf[offset:offset+scmpRawInterfaceLen], i.Ingress)
	// @ fold sl.AbsSlice_Bytes(newSlice, 0, len(newSlice))
	// @ sl.CombineRange_Bytes(buf, offset, offset+scmpRawInterfaceLen, writePerm)
	offset += scmpRawInterfaceLen
	// @ ghost newSlice = buf[offset:offset+scmpRawInterfaceLen]
	// @ sl.SplitRange_Bytes(buf, offset, offset+scmpRawInterfaceLen, writePerm)
	// @ unfold sl.AbsSlice_Bytes(newSlice, 0, len(newSlice))
	binary.BigEndian.PutUint64(buf[offset:offset+scmpRawInterfaceLen], i.Egress)
	// @ fold sl.AbsSlice_Bytes(newSlice, 0, len(newSlice))
	// @ sl.CombineRange_Bytes(buf, offset, offset+scmpRawInterfaceLen, writePerm)
	// @ sl.CombineRange_Bytes(underlyingBufRes, 0, len(buf), writePerm)
	// @ apply sl.AbsSlice_Bytes(underlyingBufRes, 0, len(underlyingBufRes)) --* b.Mem(underlyingBufRes)
	return nil /*@, underlyingBufRes@*/
}

// @ requires pb != nil
// @ preserves pb.Mem()
// @ requires sl.AbsSlice_Bytes(data, 0, len(data))
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
// @ requires  sl.AbsSlice_Bytes(data, 0, len(data))
// @ preserves df.Mem()
// @ ensures   res == nil ==> i.Mem(data)
// @ ensures   res != nil ==> (i.NonInitMem() && sl.AbsSlice_Bytes(data, 0, len(data)))
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
	// @ requires sl.AbsSlice_Bytes(data, 0, len(data))
	// @ ensures sl.AbsSlice_Bytes(data, 2, len(data))
	// @ ensures sl.AbsSlice_Bytes(data, 0, 2)
	// @ decreases
	// @ outline (
	// @ sl.SplitByIndex_Bytes(data, 0, len(data), 2, writePerm)
	// @ unfold sl.AbsSlice_Bytes(data, 0, 2)
	i.Identifier = binary.BigEndian.Uint16(data[:2])
	// @ fold sl.AbsSlice_Bytes(data, 0, 2)
	// @ )
	offset += 2
	// @ requires offset == 2
	// @ preserves acc(&i.SeqNumber)
	// @ requires len(data) >= 4
	// @ requires sl.AbsSlice_Bytes(data, 2, len(data))
	// @ ensures sl.AbsSlice_Bytes(data, 2, 4)
	// @ ensures sl.AbsSlice_Bytes(data, 4, len(data))
	// @ decreases
	// @ outline (
	// @ sl.SplitByIndex_Bytes(data, 2, len(data), 4, writePerm)
	// @ unfold sl.AbsSlice_Bytes(data, 2, 4)
	// @ assert forall i int :: { &data[offset:offset+2][i] } 0 <= i && i < 2 ==> &data[offset + i] == &data[offset : offset+2][i]
	i.SeqNumber = binary.BigEndian.Uint16(data[offset : offset+2])
	// @ fold sl.AbsSlice_Bytes(data, 2, 4)
	// @ )
	offset += 2
	// @ requires offset == 4
	// @ requires len(data) >= 4
	// @ requires acc(&i.BaseLayer)
	// @ requires sl.AbsSlice_Bytes(data, 0, 2)
	// @ requires sl.AbsSlice_Bytes(data, 2, 4)
	// @ requires sl.AbsSlice_Bytes(data, 4, len(data))
	// @ ensures  acc(i.BaseLayer.Mem(data))
	// @ decreases
	// @ outline (
	// @ sl.CombineAtIndex_Bytes(data, 0, 4, 2, writePerm)
	// @ unfold sl.AbsSlice_Bytes(data, 0, 4)
	// @ unfold sl.AbsSlice_Bytes(data, 4, len(data))
	// @ assert forall i int :: { &data[offset:][i] } 0 <= i && i < len(data) - offset ==> &data[offset:][i] == &data[offset + i]
	i.BaseLayer = BaseLayer{
		Contents: data[:offset],
		Payload:  data[offset:],
	}
	// @ assert forall l int :: { &i.Payload[l] } 0 <= l && l < len(i.Payload) ==> &data[offset+l] == &i.Payload[l]
	// @ assert forall l int :: { &i.Payload[l] } 0 <= l && l < len(i.Payload) ==> acc(&i.Payload[l])
	// @ fold sl.AbsSlice_Bytes(i.Contents, 0, len(i.Contents))
	// @ fold sl.AbsSlice_Bytes(i.Payload, 0, len(i.Payload))
	// @ fold i.BaseLayer.Mem(data)
	// @ )
	return nil
}

// SerializeTo writes the serialized form of this layer into the
// SerializationBuffer, implementing gopacket.SerializableLayer.
// @ requires b != nil
// @ requires i.Mem(ubufMem)
// @ requires b.Mem(underlyingBuf)
// @ ensures  err == nil ==> underlyingBufRes != nil
// @ ensures  err == nil ==> i.Mem(ubufMem) && b.Mem(underlyingBufRes)
// @ ensures  err != nil ==> b.Mem(underlyingBuf)
// @ ensures  err != nil ==> err.ErrorMem()
// @ decreases
func (i *SCMPEcho) SerializeTo(b gopacket.SerializeBuffer, opts gopacket.SerializeOptions /*@, ghost ubufMem []byte, ghost underlyingBuf []byte @*/) (err error /*@, ghost underlyingBufRes []byte @*/) {
	buf, err /*@, underlyingBufRes@*/ := b.PrependBytes(4 /*@, underlyingBuf@*/)
	if err != nil {
		return err /*@, underlyingBufRes@*/
	}
	offset := 0
	// @ unfold i.Mem(ubufMem)
	// @ defer fold i.Mem(ubufMem)
	// @ requires offset == 0
	// @ requires len(underlyingBufRes) >= 4
	// @ requires buf === underlyingBufRes[:4]
	// @ requires b != nil
	// @ preserves acc(&i.Identifier)
	// @ preserves b.Mem(underlyingBufRes)
	// @ decreases
	// @ outline (
	// @ b.ExchangePred(underlyingBufRes)
	// @ sl.SplitByIndex_Bytes(underlyingBufRes, 0, len(underlyingBufRes), 2, writePerm)
	// @ unfold sl.AbsSlice_Bytes(underlyingBufRes, 0, 2)
	binary.BigEndian.PutUint16(buf[:2], i.Identifier)
	// @ fold sl.AbsSlice_Bytes(underlyingBufRes, 0, 2)
	// @ sl.CombineAtIndex_Bytes(underlyingBufRes, 0, len(underlyingBufRes), 2, writePerm)
	// @ apply sl.AbsSlice_Bytes(underlyingBufRes, 0, len(underlyingBufRes)) --* b.Mem(underlyingBufRes)
	// @ )
	offset += 2
	// @ requires offset == 2
	// @ requires len(underlyingBufRes) >= 4
	// @ requires buf === underlyingBufRes[:4]
	// @ requires b != nil
	// @ preserves acc(&i.SeqNumber)
	// @ preserves b.Mem(underlyingBufRes)
	// @ decreases
	// @ outline (
	// @ b.ExchangePred(underlyingBufRes)
	// @ sl.SplitByIndex_Bytes(underlyingBufRes, 0, len(underlyingBufRes), 2, writePerm)
	// @ sl.SplitByIndex_Bytes(underlyingBufRes, 2, len(underlyingBufRes), 4, writePerm)
	// @ unfold sl.AbsSlice_Bytes(underlyingBufRes, 2, 4)
	// @ assert forall i int :: { &buf[offset:offset+2][i] } 0 <= i && i < 2 ==> &buf[offset:offset+2][i] == &buf[offset + i]
	binary.BigEndian.PutUint16(buf[offset:offset+2], i.SeqNumber)
	// @ fold sl.AbsSlice_Bytes(underlyingBufRes, 2, 4)
	// @ sl.CombineAtIndex_Bytes(underlyingBufRes, 2, len(underlyingBufRes), 4, writePerm)
	// @ sl.CombineAtIndex_Bytes(underlyingBufRes, 0, len(underlyingBufRes), 2, writePerm)
	// @ apply sl.AbsSlice_Bytes(underlyingBufRes, 0, len(underlyingBufRes)) --* b.Mem(underlyingBufRes)
	// @ )
	return nil /*@, underlyingBufRes@*/
}

// @ requires pb != nil
// @ preserves pb.Mem()
// @ requires sl.AbsSlice_Bytes(data, 0, len(data))
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
// @ requires  sl.AbsSlice_Bytes(data, 0, len(data))
// @ preserves df.Mem()
// @ ensures   res == nil ==> i.Mem(data)
// @ ensures   res != nil ==> (i.NonInitMem() && sl.AbsSlice_Bytes(data, 0, len(data)))
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
	// @ preserves sl.AbsSlice_Bytes(data, 0, len(data))
	// @ decreases
	// @ outline (
	// @ sl.SplitByIndex_Bytes(data, 0, len(data), 2, writePerm)
	// @ sl.SplitByIndex_Bytes(data, 2, len(data), 4, writePerm)
	// @ unfold sl.AbsSlice_Bytes(data, 2, 4)
	// @ assert forall i int :: { &data[2:4][i] } 0 <= i && i < 2 ==> &data[2:4][i] == &data[2 + i]
	i.Pointer = binary.BigEndian.Uint16(data[2:4])
	// @ fold sl.AbsSlice_Bytes(data, 2, 4)
	// @ sl.CombineAtIndex_Bytes(data, 0, 4, 2, writePerm)
	// @ sl.CombineAtIndex_Bytes(data, 0, len(data), 4, writePerm)
	// @ )
	// @ requires len(data) >= 4
	// @ requires acc(&i.BaseLayer)
	// @ ensures  i.BaseLayer.Mem(data)
	// @ requires sl.AbsSlice_Bytes(data, 0, len(data))
	// @ decreases
	// @ outline (
	// @ unfold sl.AbsSlice_Bytes(data, 0, len(data))
	// @ assert forall i int :: { &data[4:][i] } 0 <= i && i < len(data) ==> &data[4:][i] == &data[4 + i]
	i.BaseLayer = BaseLayer{
		Contents: data[:4],
		Payload:  data[4:],
	}
	// @ assert forall l int :: { &i.Payload[l] } 0 <= l && l < len(i.Payload) ==> &data[4+l] == &i.Payload[l]
	// @ fold sl.AbsSlice_Bytes(i.Contents, 0, len(i.Contents))
	// @ fold sl.AbsSlice_Bytes(i.Payload, 0, len(i.Payload))
	// @ fold i.BaseLayer.Mem(data)
	// @ )
	return nil
}

// SerializeTo writes the serialized form of this layer into the
// SerializationBuffer, implementing gopacket.SerializableLayer.
// @ requires b != nil
// @ requires i.Mem(ubufMem)
// @ requires b.Mem(underlyingBuf)
// @ ensures err == nil ==> underlyingBufRes != nil
// @ ensures err == nil ==> i.Mem(ubufMem) && b.Mem(underlyingBufRes)
// @ ensures err != nil ==> b.Mem(underlyingBuf)
// @ ensures err != nil ==> err.ErrorMem()
// @ decreases
func (i *SCMPParameterProblem) SerializeTo(b gopacket.SerializeBuffer, opts gopacket.SerializeOptions /*@, ghost ubufMem []byte, ghost underlyingBuf []byte @*/) (err error /*@, ghost underlyingBufRes []byte @*/) {

	buf, err /*@, underlyingBufRes@*/ := b.PrependBytes(2 + 2 /*@, underlyingBuf@*/)
	if err != nil {
		return err /*@, underlyingBufRes@*/
	}
	// @ unfold i.Mem(ubufMem)
	// @ defer fold i.Mem(ubufMem)
	// @ requires len(underlyingBufRes) >= 4
	// @ requires buf === underlyingBufRes[:4]
	// @ requires b != nil
	// @ preserves b.Mem(underlyingBufRes)
	// @ decreases
	// @ outline (
	// @ b.ExchangePred(underlyingBufRes)
	// @ sl.SplitByIndex_Bytes(underlyingBufRes, 0, len(underlyingBufRes), 2, writePerm)
	// @ unfold sl.AbsSlice_Bytes(underlyingBufRes, 0, 2)
	binary.BigEndian.PutUint16(buf[0:2], uint16(0)) //Reserved
	// @ fold sl.AbsSlice_Bytes(underlyingBufRes, 0, 2)
	// @ sl.CombineAtIndex_Bytes(underlyingBufRes, 0, len(underlyingBufRes), 2, writePerm)
	// @ apply sl.AbsSlice_Bytes(underlyingBufRes, 0, len(underlyingBufRes)) --* b.Mem(underlyingBufRes)
	// @ )
	// @ requires len(underlyingBufRes) >= 4
	// @ requires buf === underlyingBufRes[:4]
	// @ requires b != nil
	// @ preserves acc(&i.Pointer)
	// @ preserves b.Mem(underlyingBufRes)
	// @ decreases
	// @ outline (
	// @ b.ExchangePred(underlyingBufRes)
	// @ sl.SplitByIndex_Bytes(underlyingBufRes, 0, len(underlyingBufRes), 2, writePerm)
	// @ sl.SplitByIndex_Bytes(underlyingBufRes, 2, len(underlyingBufRes), 4, writePerm)
	// @ unfold sl.AbsSlice_Bytes(underlyingBufRes, 2, 4)
	// @ assert forall i int :: { &buf[2:4][i] } 0 <= i && i < 2 ==> &buf[2:4][i] == &buf[2 + i]
	binary.BigEndian.PutUint16(buf[2:4], i.Pointer)
	// @ fold sl.AbsSlice_Bytes(underlyingBufRes, 2, 4)
	// @ sl.CombineAtIndex_Bytes(underlyingBufRes, 2, len(underlyingBufRes), 4, writePerm)
	// @ sl.CombineAtIndex_Bytes(underlyingBufRes, 0, len(underlyingBufRes), 2, writePerm)
	// @ apply sl.AbsSlice_Bytes(underlyingBufRes, 0, len(underlyingBufRes)) --* b.Mem(underlyingBufRes)
	// @ )
	return nil /*@, underlyingBufRes@*/
}

// @ requires  pb != nil
// @ preserves pb.Mem()
// @ requires  sl.AbsSlice_Bytes(data, 0, len(data))
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
// @ requires  sl.AbsSlice_Bytes(data, 0, len(data))
// @ preserves df.Mem()
// @ ensures   res == nil ==> i.Mem(data)
// @ ensures   res != nil ==> (i.NonInitMem() && sl.AbsSlice_Bytes(data, 0, len(data)))
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
	// @ requires sl.AbsSlice_Bytes(data, 0, len(data))
	// @ ensures sl.AbsSlice_Bytes(data, 0, 2)
	// @ ensures sl.AbsSlice_Bytes(data, 2, len(data))
	// @ decreases
	// @ outline (
	// @ sl.SplitByIndex_Bytes(data, 0, len(data), 2, writePerm)
	// @ unfold sl.AbsSlice_Bytes(data, 0, 2)
	i.Identifier = binary.BigEndian.Uint16(data[offset : offset+2])
	// @ fold sl.AbsSlice_Bytes(data, 0, 2)
	// @ )
	offset += 2
	// @ requires offset == 2
	// @ preserves acc(&i.Sequence)
	// @ requires len(data) >= 2 + 2 + addr.IABytes + scmpRawInterfaceLen
	// @ requires sl.AbsSlice_Bytes(data, 2, len(data))
	// @ ensures sl.AbsSlice_Bytes(data, 2, 2+2)
	// @ ensures sl.AbsSlice_Bytes(data, 2+2, len(data))
	// @ decreases
	// @ outline (
	// @ sl.SplitByIndex_Bytes(data, 2, len(data), 2+2, writePerm)
	// @ unfold sl.AbsSlice_Bytes(data, 2, 2+2)
	// @ assert forall i int :: { &data[offset:offset+2][i] } 0 <= i && i < 2 ==> &data[offset + i] == &data[offset : offset+2][i]
	i.Sequence = binary.BigEndian.Uint16(data[offset : offset+2])
	// @ fold sl.AbsSlice_Bytes(data, 2, 2+2)
	// @ )
	offset += 2
	// @ requires offset == 2 + 2
	// @ preserves acc(&i.IA)
	// @ requires len(data) >= 2 + 2 + addr.IABytes + scmpRawInterfaceLen
	// @ requires sl.AbsSlice_Bytes(data, 2+2, len(data))
	// @ ensures sl.AbsSlice_Bytes(data, 2+2, 2+2+addr.IABytes)
	// @ ensures sl.AbsSlice_Bytes(data, 2+2+addr.IABytes, len(data))
	// @ decreases
	// @ outline (
	// @ sl.SplitByIndex_Bytes(data, 2+2, len(data), 2+2+addr.IABytes, writePerm)
	// @ unfold sl.AbsSlice_Bytes(data, 2+2, 2+2+addr.IABytes)
	// @ assert forall i int :: { &data[offset:offset+addr.IABytes][i] } 0 <= i && i < addr.IABytes ==> &data[offset + i] == &data[offset : offset+addr.IABytes][i]
	i.IA = addr.IA(binary.BigEndian.Uint64(data[offset : offset+addr.IABytes]))
	// @ fold sl.AbsSlice_Bytes(data, 2+2, 2+2+addr.IABytes)
	// @ )
	offset += addr.IABytes
	// @ requires offset == 2 + 2 + addr.IABytes
	// @ preserves acc(&i.Interface)
	// @ requires len(data) >= 2 + 2 + addr.IABytes + scmpRawInterfaceLen
	// @ requires sl.AbsSlice_Bytes(data, 2+2+addr.IABytes, len(data))
	// @ ensures sl.AbsSlice_Bytes(data, 2+2+addr.IABytes, 2+2+addr.IABytes+scmpRawInterfaceLen)
	// @ ensures sl.AbsSlice_Bytes(data, 2+2+addr.IABytes+scmpRawInterfaceLen, len(data))
	// @ decreases
	// @ outline (
	// @ sl.SplitByIndex_Bytes(data, 2+2+addr.IABytes, len(data), 2+2+addr.IABytes+scmpRawInterfaceLen, writePerm)
	// @ unfold sl.AbsSlice_Bytes(data, 2+2+addr.IABytes, 2+2+addr.IABytes+scmpRawInterfaceLen)
	// @ assert forall i int :: { &data[offset:offset+scmpRawInterfaceLen][i] } 0 <= i && i < scmpRawInterfaceLen ==> &data[offset + i] == &data[offset : offset+addr.IABytes][i]
	i.Interface = binary.BigEndian.Uint64(data[offset : offset+scmpRawInterfaceLen])
	// @ fold sl.AbsSlice_Bytes(data, 2+2+addr.IABytes, 2+2+addr.IABytes+scmpRawInterfaceLen)
	// @ )
	offset += scmpRawInterfaceLen
	// @ requires offset == 2 + 2 + addr.IABytes + scmpRawInterfaceLen
	// @ requires len(data) >= 2 + 2 + addr.IABytes + scmpRawInterfaceLen
	// @ requires acc(&i.BaseLayer)
	// @ requires sl.AbsSlice_Bytes(data, 0, 2)
	// @ requires sl.AbsSlice_Bytes(data, 2, 2+2)
	// @ requires sl.AbsSlice_Bytes(data, 2+2, 2+2+addr.IABytes)
	// @ requires sl.AbsSlice_Bytes(data, 2+2+addr.IABytes, 2+2+addr.IABytes+scmpRawInterfaceLen)
	// @ requires sl.AbsSlice_Bytes(data, 2+2+addr.IABytes+scmpRawInterfaceLen, len(data))
	// @ ensures  i.BaseLayer.Mem(data)
	// @ decreases
	// @ outline (
	// @ sl.CombineAtIndex_Bytes(data, 0, 2+2, 2, writePerm)
	// @ sl.CombineAtIndex_Bytes(data, 0, 2+2+addr.IABytes, 2+2, writePerm)
	// @ sl.CombineAtIndex_Bytes(data, 0, 2+2+addr.IABytes+scmpRawInterfaceLen, 2+2+addr.IABytes, writePerm)
	// @ unfold sl.AbsSlice_Bytes(data, 0, 2+2+addr.IABytes+scmpRawInterfaceLen)
	// @ unfold sl.AbsSlice_Bytes(data, 2+2+addr.IABytes+scmpRawInterfaceLen, len(data))
	// @ assert forall i int :: { &data[offset:][i] } 0 <= i && i < len(data)-offset ==> &data[offset:][i] == &data[offset + i]
	// @ assert forall l int :: { &data[l] } offset <= l && l < len(data) ==> acc(&data[l])
	i.BaseLayer = BaseLayer{
		Contents: data[:offset],
		Payload:  data[offset:],
	}
	// @ assert forall l int :: { &i.Payload[l] } 0 <= l && l < len(i.Payload) ==> &data[offset+l] == &i.Payload[l]
	// @ fold sl.AbsSlice_Bytes(i.Contents, 0, len(i.Contents))
	// @ fold sl.AbsSlice_Bytes(i.Payload, 0, len(i.Payload))
	// @ fold i.BaseLayer.Mem(data)
	// @ )
	return nil
}

// SerializeTo writes the serialized form of this layer into the
// SerializationBuffer, implementing gopacket.SerializableLayer.
// @ requires b != nil
// @ requires i.Mem(ubufMem)
// @ requires b.Mem(underlyingBuf)
// @ ensures err == nil ==> underlyingBufRes != nil
// @ ensures err == nil ==> i.Mem(ubufMem) && b.Mem(underlyingBufRes)
// @ ensures err != nil ==> b.Mem(underlyingBuf)
// @ ensures err != nil ==> err.ErrorMem()
// @ decreases
func (i *SCMPTraceroute) SerializeTo(b gopacket.SerializeBuffer, opts gopacket.SerializeOptions /*@, ghost ubufMem []byte, ghost underlyingBuf []byte @*/) (err error /*@, ghost underlyingBufRes []byte @*/) {

	buf, err /*@, underlyingBufRes@*/ := b.PrependBytes(2 + 2 + addr.IABytes + scmpRawInterfaceLen /*@, underlyingBuf@*/)
	if err != nil {
		return err /*@, underlyingBufRes@*/
	}
	offset := 0
	// @ unfold i.Mem(ubufMem)
	// @ defer fold i.Mem(ubufMem)
	// @ requires offset == 0
	// @ requires len(underlyingBufRes) >= 2 + 2 + addr.IABytes + scmpRawInterfaceLen
	// @ requires buf === underlyingBufRes[:2+2+addr.IABytes+scmpRawInterfaceLen]
	// @ requires b != nil
	// @ preserves acc(&i.Identifier)
	// @ preserves b.Mem(underlyingBufRes)
	// @ decreases
	// @ outline (
	// @ b.ExchangePred(underlyingBufRes)
	// @ sl.SplitByIndex_Bytes(underlyingBufRes, 0, len(underlyingBufRes), 2, writePerm)
	// @ unfold sl.AbsSlice_Bytes(underlyingBufRes, 0, 2)
	binary.BigEndian.PutUint16(buf[:2], i.Identifier)
	// @ fold sl.AbsSlice_Bytes(underlyingBufRes, 0, 2)
	// @ sl.CombineAtIndex_Bytes(underlyingBufRes, 0, len(underlyingBufRes), 2, writePerm)
	// @ apply sl.AbsSlice_Bytes(underlyingBufRes, 0, len(underlyingBufRes)) --* b.Mem(underlyingBufRes)
	// @ )
	offset += 2
	// @ requires offset == 2
	// @ requires len(underlyingBufRes) >= 2 + 2 + addr.IABytes + scmpRawInterfaceLen
	// @ requires buf === underlyingBufRes[:2 + 2 + addr.IABytes + scmpRawInterfaceLen]
	// @ requires b != nil
	// @ preserves acc(&i.Sequence)
	// @ preserves b.Mem(underlyingBufRes)
	// @ decreases
	// @ outline (
	// @ b.ExchangePred(underlyingBufRes)
	// @ sl.SplitByIndex_Bytes(underlyingBufRes, 0, len(underlyingBufRes), 2, writePerm)
	// @ sl.SplitByIndex_Bytes(underlyingBufRes, 2, len(underlyingBufRes), 2+2, writePerm)
	// @ unfold sl.AbsSlice_Bytes(underlyingBufRes, 2, 2+2)
	// @ assert forall i int :: { &buf[offset:offset+2][i] } 0 <= i && i < 2 ==> &buf[offset:offset+2][i] == &buf[offset + i]
	binary.BigEndian.PutUint16(buf[offset:offset+2], i.Sequence)
	// @ fold sl.AbsSlice_Bytes(underlyingBufRes, 2, 2+2)
	// @ sl.CombineAtIndex_Bytes(underlyingBufRes, 2, len(underlyingBufRes), 2+2, writePerm)
	// @ sl.CombineAtIndex_Bytes(underlyingBufRes, 0, len(underlyingBufRes), 2, writePerm)
	// @ apply sl.AbsSlice_Bytes(underlyingBufRes, 0, len(underlyingBufRes)) --* b.Mem(underlyingBufRes)
	// @ )
	offset += 2
	// @ requires offset == 2 + 2
	// @ requires len(underlyingBufRes) >= 2 + 2 + addr.IABytes + scmpRawInterfaceLen
	// @ requires buf === underlyingBufRes[:2 + 2 + addr.IABytes + scmpRawInterfaceLen]
	// @ requires b != nil
	// @ preserves acc(&i.IA)
	// @ preserves b.Mem(underlyingBufRes)
	// @ decreases
	// @ outline (
	// @ b.ExchangePred(underlyingBufRes)
	// @ sl.SplitByIndex_Bytes(underlyingBufRes, 0, len(underlyingBufRes), 2+2, writePerm)
	// @ sl.SplitByIndex_Bytes(underlyingBufRes, 2+2, len(underlyingBufRes), 2+2+addr.IABytes, writePerm)
	// @ unfold sl.AbsSlice_Bytes(underlyingBufRes, 2+2, 2+2+addr.IABytes)
	// @ assert forall i int :: { &buf[offset:offset+addr.IABytes][i] } 0 <= i && i < addr.IABytes ==> &buf[offset:offset+addr.IABytes][i] == &buf[offset + i]
	binary.BigEndian.PutUint64(buf[offset:offset+addr.IABytes], uint64(i.IA))
	// @ fold sl.AbsSlice_Bytes(underlyingBufRes, 2+2, 2+2+addr.IABytes)
	// @ sl.CombineAtIndex_Bytes(underlyingBufRes, 2+2, len(underlyingBufRes), 2+2+addr.IABytes, writePerm)
	// @ sl.CombineAtIndex_Bytes(underlyingBufRes, 0, len(underlyingBufRes), 2+2, writePerm)
	// @ apply sl.AbsSlice_Bytes(underlyingBufRes, 0, len(underlyingBufRes)) --* b.Mem(underlyingBufRes)
	// @ )
	offset += addr.IABytes
	// @ requires offset == 2 + 2 + addr.IABytes
	// @ requires len(underlyingBufRes) >= 2 + 2 + addr.IABytes + scmpRawInterfaceLen
	// @ requires buf === underlyingBufRes[:2 + 2 + addr.IABytes + scmpRawInterfaceLen]
	// @ requires b != nil
	// @ preserves acc(&i.Interface)
	// @ preserves b.Mem(underlyingBufRes)
	// @ decreases
	// @ outline (
	// @ b.ExchangePred(underlyingBufRes)
	// @ sl.SplitByIndex_Bytes(underlyingBufRes, 0, len(underlyingBufRes), 2+2+addr.IABytes, writePerm)
	// @ sl.SplitByIndex_Bytes(underlyingBufRes, 2+2+addr.IABytes, len(underlyingBufRes), 2+2+addr.IABytes+scmpRawInterfaceLen, writePerm)
	// @ unfold sl.AbsSlice_Bytes(underlyingBufRes, 2+2+addr.IABytes, 2+2+addr.IABytes+scmpRawInterfaceLen)
	// @ assert forall i int :: { &buf[offset:offset+scmpRawInterfaceLen][i] } 0 <= i && i < scmpRawInterfaceLen ==> &buf[offset:offset+scmpRawInterfaceLen][i] == &buf[offset + i]
	binary.BigEndian.PutUint64(buf[offset:offset+scmpRawInterfaceLen], i.Interface)
	// @ fold sl.AbsSlice_Bytes(underlyingBufRes, 2+2+addr.IABytes, 2+2+addr.IABytes+scmpRawInterfaceLen)
	// @ sl.CombineAtIndex_Bytes(underlyingBufRes, 2+2+addr.IABytes, len(underlyingBufRes), 2+2+addr.IABytes+scmpRawInterfaceLen, writePerm)
	// @ sl.CombineAtIndex_Bytes(underlyingBufRes, 0, len(underlyingBufRes), 2+2+addr.IABytes, writePerm)
	// @ apply sl.AbsSlice_Bytes(underlyingBufRes, 0, len(underlyingBufRes)) --* b.Mem(underlyingBufRes)
	// @ )
	return nil /*@, underlyingBufRes@*/
}

// @ requires  pb != nil
// @ preserves pb.Mem()
// @ requires  sl.AbsSlice_Bytes(data, 0, len(data))
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
// @ requires  sl.AbsSlice_Bytes(data, 0, len(data))
// @ preserves df.Mem()
// @ ensures   res == nil ==> i.Mem(data)
// @ ensures   res != nil ==> (i.NonInitMem() && sl.AbsSlice_Bytes(data, 0, len(data)))
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
	// @ defer fold i.BaseLayer.Mem(data)
	// @ unfold sl.AbsSlice_Bytes(data, 0, len(data))
	// @ assert forall i int :: { &data[minLength:][i] } 0 <= i && i < len(data) - minLength ==> &data[minLength:][i] == &data[minLength + i]
	i.BaseLayer = BaseLayer{
		Contents: data[:minLength],
		Payload:  data[minLength:],
	}
	// @ assert forall l int :: { &i.Payload[l] } 0 <= l && l < len(i.Payload) ==> &data[minLength:][l] == &i.Payload[l]
	// @ fold sl.AbsSlice_Bytes(i.Contents, 0, len(i.Contents))
	// @ fold sl.AbsSlice_Bytes(i.Payload, 0, len(i.Payload))
	return nil
}

// SerializeTo writes the serialized form of this layer into the
// SerializationBuffer, implementing gopacket.SerializableLayer.
// @ requires b != nil
// @ requires i.Mem(ubufMem)
// @ requires b.Mem(underlyingBuf)
// @ ensures err == nil ==> underlyingBufRes != nil
// @ ensures err == nil ==> i.Mem(ubufMem) && b.Mem(underlyingBufRes)
// @ ensures err != nil ==> b.Mem(underlyingBuf)
// @ ensures err != nil ==> err.ErrorMem()
// @ decreases
func (i *SCMPDestinationUnreachable) SerializeTo(b gopacket.SerializeBuffer, opts gopacket.SerializeOptions /*@, ghost ubufMem []byte, ghost underlyingBuf []byte @*/) (err error /*@, ghost underlyingBufRes []byte @*/) {

	buf, err /*@, underlyingBufRes@*/ := b.PrependBytes(4 /*@, underlyingBuf@*/)
	if err != nil {
		return err /*@, underlyingBufRes@*/
	}
	// @ assert buf === underlyingBufRes[:4]
	// @ b.ExchangePred(underlyingBufRes)
	// @ sl.SplitByIndex_Bytes(underlyingBufRes, 0, len(underlyingBufRes), 4, writePerm)
	// @ unfold sl.AbsSlice_Bytes(underlyingBufRes, 0, 4)
	copy(buf, make([]byte, 4) /*@, writePerm@*/)
	// @ fold sl.AbsSlice_Bytes(underlyingBufRes, 0, 4)
	// @ sl.CombineAtIndex_Bytes(underlyingBufRes, 0, len(underlyingBufRes), 4, writePerm)
	// @ apply sl.AbsSlice_Bytes(underlyingBufRes, 0, len(underlyingBufRes)) --* b.Mem(underlyingBufRes)
	return nil /*@, underlyingBufRes@*/
}

// @ requires  pb != nil
// @ requires  sl.AbsSlice_Bytes(data, 0, len(data))
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
// @ requires  sl.AbsSlice_Bytes(data, 0, len(data))
// @ requires  i.NonInitMem()
// @ preserves df.Mem()
// @ ensures   res == nil ==> i.Mem(data)
// @ ensures   res != nil ==> (i.NonInitMem() && sl.AbsSlice_Bytes(data, 0, len(data)))
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
	// @ preserves sl.AbsSlice_Bytes(data, 0, len(data))
	// @ decreases
	// @ outline (
	// @ sl.SplitByIndex_Bytes(data, 0, len(data), 2, writePerm)
	// @ sl.SplitByIndex_Bytes(data, 2, len(data), 4, writePerm)
	// @ unfold sl.AbsSlice_Bytes(data, 2, 4)
	// @ assert forall i int :: { &data[2:4][i] } 0 <= i && i < 2 ==> &data[2:4][i] == &data[2 + i]
	i.MTU = binary.BigEndian.Uint16(data[2:4])
	// @ fold sl.AbsSlice_Bytes(data, 2, 4)
	// @ sl.CombineAtIndex_Bytes(data, 0, 4, 2, writePerm)
	// @ sl.CombineAtIndex_Bytes(data, 0, len(data), 4, writePerm)
	// @ )
	// @ requires len(data) >= 4
	// @ requires acc(&i.BaseLayer)
	// @ requires sl.AbsSlice_Bytes(data, 0, len(data))
	// @ ensures  i.BaseLayer.Mem(data)
	// @ decreases
	// @ outline (
	// @ unfold sl.AbsSlice_Bytes(data, 0, len(data))
	// @ assert forall i int :: { &data[4:][i] } 0 <= i && i < len(data) ==> &data[4:][i] == &data[4 + i]
	i.BaseLayer = BaseLayer{
		Contents: data[:4],
		Payload:  data[4:],
	}
	// @ assert forall l int :: { &i.Payload[l] } 0 <= l && l < len(i.Payload) ==> &data[4+l] == &i.Payload[l]
	// @ fold sl.AbsSlice_Bytes(i.Contents, 0, len(i.Contents))
	// @ fold sl.AbsSlice_Bytes(i.Payload, 0, len(i.Payload))
	// @ fold i.BaseLayer.Mem(data)
	// @ )
	return nil
}

// SerializeTo writes the serialized form of this layer into the
// SerializationBuffer, implementing gopacket.SerializableLayer.
// @ requires b != nil
// @ requires i.Mem(ubufMem)
// @ requires b.Mem(underlyingBuf)
// @ ensures err == nil ==> underlyingBufRes != nil
// @ ensures err == nil ==> i.Mem(ubufMem) && b.Mem(underlyingBufRes)
// @ ensures err != nil ==> b.Mem(underlyingBuf)
// @ ensures err != nil ==> err.ErrorMem()
// @ decreases
func (i *SCMPPacketTooBig) SerializeTo(b gopacket.SerializeBuffer, opts gopacket.SerializeOptions /*@, ghost ubufMem []byte, ghost underlyingBuf []byte @*/) (err error /*@, ghost underlyingBufRes []byte @*/) {

	buf, err /*@, underlyingBufRes@*/ := b.PrependBytes(2 + 2 /*@, underlyingBuf@*/)
	if err != nil {
		return err /*@, underlyingBufRes@*/
	}
	// @ unfold i.Mem(ubufMem)
	// @ defer fold i.Mem(ubufMem)
	// @ requires len(underlyingBufRes) >= 4
	// @ requires buf === underlyingBufRes[:4]
	// @ requires b != nil
	// @ preserves b.Mem(underlyingBufRes)
	// @ decreases
	// @ outline (
	// @ b.ExchangePred(underlyingBufRes)
	// @ sl.SplitByIndex_Bytes(underlyingBufRes, 0, len(underlyingBufRes), 2, writePerm)
	// @ unfold sl.AbsSlice_Bytes(underlyingBufRes, 0, 2)
	binary.BigEndian.PutUint16(buf[0:2], uint16(0)) //Reserved
	// @ fold sl.AbsSlice_Bytes(underlyingBufRes, 0, 2)
	// @ sl.CombineAtIndex_Bytes(underlyingBufRes, 0, len(underlyingBufRes), 2, writePerm)
	// @ apply sl.AbsSlice_Bytes(underlyingBufRes, 0, len(underlyingBufRes)) --* b.Mem(underlyingBufRes)
	// @ )
	// @ requires len(underlyingBufRes) >= 4
	// @ requires buf === underlyingBufRes[:4]
	// @ requires b != nil
	// @ preserves acc(&i.MTU)
	// @ preserves b.Mem(underlyingBufRes)
	// @ decreases
	// @ outline (
	// @ b.ExchangePred(underlyingBufRes)
	// @ sl.SplitByIndex_Bytes(underlyingBufRes, 0, len(underlyingBufRes), 2, writePerm)
	// @ sl.SplitByIndex_Bytes(underlyingBufRes, 2, len(underlyingBufRes), 4, writePerm)
	// @ unfold sl.AbsSlice_Bytes(underlyingBufRes, 2, 4)
	// @ assert forall i int :: { &buf[2:4][i] } 0 <= i && i < 2 ==> &buf[2:4][i] == &buf[2 + i]
	binary.BigEndian.PutUint16(buf[2:4], i.MTU)
	// @ fold sl.AbsSlice_Bytes(underlyingBufRes, 2, 4)
	// @ sl.CombineAtIndex_Bytes(underlyingBufRes, 2, len(underlyingBufRes), 4, writePerm)
	// @ sl.CombineAtIndex_Bytes(underlyingBufRes, 0, len(underlyingBufRes), 2, writePerm)
	// @ apply sl.AbsSlice_Bytes(underlyingBufRes, 0, len(underlyingBufRes)) --* b.Mem(underlyingBufRes)
	// @ )
	return nil /*@, underlyingBufRes@*/
}

// @ requires  pb != nil
// @ preserves pb.Mem()
// @ requires  sl.AbsSlice_Bytes(data, 0, len(data))
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
