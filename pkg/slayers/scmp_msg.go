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
	//@ "github.com/scionproto/scion/verification/utils/slices"
)

const scmpRawInterfaceLen = 8

// SCMPExternalInterfaceDown message contains the data for that error.
//
//   0                   1                   2                   3
//   0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
//  +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//  |              ISD              |                               |
//  +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+         AS                    +
//  |                                                               |
//  +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//  |                                                               |
//  +                        Interface ID                           +
//  |                                                               |
//  +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//
type SCMPExternalInterfaceDown struct {
	BaseLayer
	
	IA   addr.IA
	IfID uint64
}

// LayerType returns LayerTypeSCMPExternalInterfaceDown
//@ decreases
//@ pure
func (i *SCMPExternalInterfaceDown) LayerType() gopacket.LayerType {
	// (VerifiedSCION) TODO: replace with global
	return getLayerTypeSCMPExternalInterfaceDown()
}

// NextLayerType returns the layer type contained by this DecodingLayer.
//@ preserves acc(&gopacket.LayerTypePayload, _)
//@ decreases
func (i *SCMPExternalInterfaceDown) NextLayerType() gopacket.LayerType {
	return gopacket.LayerTypePayload
}

// DecodeFromBytes decodes the given bytes into this layer.
//@ requires df != nil
//@ requires df.Mem()
//@ requires slices.AbsSlice_Bytes(data, 0, len(data))
//@ requires i.Mem()
//@ ensures i.Mem()
//@ ensures df.Mem()
//@ ensures res != nil ==> slices.AbsSlice_Bytes(data, 0, len(data))
//@ ensures res != nil ==> res.ErrorMem()
//@ decreases
func (i *SCMPExternalInterfaceDown) DecodeFromBytes(data []byte,
	df gopacket.DecodeFeedback) (res error) {

	minLength := addr.IABytes + scmpRawInterfaceLen
	if size := len(data); size < minLength {
		df.SetTruncated()
		return serrors.New("buffer too short", "mininum_legth", minLength, "actual", size)
	}
	//@ unfold i.Mem()
	//@ defer fold i.Mem()
	offset := 0
	//@ requires offset == 0
	//@ requires acc(&i.IA)
	//@ requires len(data) >= addr.IABytes + scmpRawInterfaceLen
	//@ requires slices.AbsSlice_Bytes(data, 0, len(data))
	//@ ensures slices.AbsSlice_Bytes(data, addr.IABytes, len(data))
	//@ ensures slices.AbsSlice_Bytes(data, 0, addr.IABytes)
	//@ ensures acc(&i.IA)
	//@ decreases
	//@ outline (
	//@ slices.SplitByIndex_Bytes(data, 0, len(data), addr.IABytes, writePerm)
	//@ unfold slices.AbsSlice_Bytes(data, 0, addr.IABytes)
	i.IA = addr.IA(binary.BigEndian.Uint64(data[offset:]))
	//@ fold slices.AbsSlice_Bytes(data, 0, addr.IABytes)
	//@ )
	offset += addr.IABytes
	//@ requires offset == addr.IABytes
	//@ requires acc(&i.IfID)
	//@ requires len(data) >= addr.IABytes + scmpRawInterfaceLen
	//@ requires slices.AbsSlice_Bytes(data, addr.IABytes, len(data))
	//@ ensures slices.AbsSlice_Bytes(data, addr.IABytes, addr.IABytes+scmpRawInterfaceLen)
	//@ ensures slices.AbsSlice_Bytes(data, addr.IABytes+scmpRawInterfaceLen, len(data))
	//@ ensures acc(&i.IfID)
	//@ decreases
	//@ outline (
	//@ slices.SplitByIndex_Bytes(data, addr.IABytes, len(data), addr.IABytes+scmpRawInterfaceLen, writePerm)
	//@ unfold slices.AbsSlice_Bytes(data, addr.IABytes, addr.IABytes+scmpRawInterfaceLen)
	//@ assert forall i int :: 0 <= i && i < scmpRawInterfaceLen ==> &data[offset + i] == &data[offset : offset+scmpRawInterfaceLen][i]
	i.IfID = binary.BigEndian.Uint64(data[offset : offset+scmpRawInterfaceLen])
	//@ fold slices.AbsSlice_Bytes(data, addr.IABytes, addr.IABytes+scmpRawInterfaceLen)
	//@ )
	offset += scmpRawInterfaceLen
	//@ requires offset == addr.IABytes + scmpRawInterfaceLen
	//@ requires len(data) >= addr.IABytes + scmpRawInterfaceLen
	//@ requires i.BaseLayer.Mem()
	//@ requires slices.AbsSlice_Bytes(data, 0, addr.IABytes)
	//@ requires slices.AbsSlice_Bytes(data, addr.IABytes, addr.IABytes+scmpRawInterfaceLen)
	//@ requires slices.AbsSlice_Bytes(data, addr.IABytes+scmpRawInterfaceLen, len(data))
	//@ ensures i.BaseLayer.Mem()
	//@ decreases
	//@ outline (
	//@ slices.CombineAtIndex_Bytes(data, 0, addr.IABytes+scmpRawInterfaceLen, addr.IABytes, writePerm)
	//@ unfold slices.AbsSlice_Bytes(data, 0, addr.IABytes+scmpRawInterfaceLen)
	//@ unfold slices.AbsSlice_Bytes(data, addr.IABytes+scmpRawInterfaceLen, len(data))
	//@ unfold i.BaseLayer.Mem()
	//@ assert forall i int :: offset <= i && i < len(data) ==> &data[offset:][i] == &data[offset + i]
	i.BaseLayer = BaseLayer{
		Contents: data[:offset],
		Payload:  data[offset:],
	}
	//@ assert forall l int :: 0 <= l && l < len(i.Payload) ==> &data[offset+l] == &i.Payload[l]
	//@ fold slices.AbsSlice_Bytes(i.Contents, 0, len(i.Contents))
	//@ fold slices.AbsSlice_Bytes(i.Payload, 0, len(i.Payload))
	//@ fold i.BaseLayer.Mem()
	//@ )
	return nil
}

// SerializeTo writes the serialized form of this layer into the
// SerializationBuffer, implementing gopacket.SerializableLayer.
//@ requires b != nil
//@ requires i.Mem()
//@ requires b.Mem(buf_init)
//@ ensures err == nil ==> buf_res != nil
//@ ensures err == nil ==> i.Mem() && b.Mem(buf_res)
//@ ensures err != nil ==> b.Mem(buf_init)
//@ ensures err != nil ==> err.ErrorMem()
//@ decreases
func (i *SCMPExternalInterfaceDown) SerializeTo(b gopacket.SerializeBuffer, opts gopacket.SerializeOptions/*@, ghost buf_init []byte @*/) (err error/*@, ghost buf_res []byte @*/) {

	buf, err/*@, buf_res@*/ := b.PrependBytes(addr.IABytes + scmpRawInterfaceLen/*@, buf_init@*/)
	if err != nil {
		return err/*@, buf_res @*/
	}
	offset := 0
	//@ unfold i.Mem()
	//@ defer fold i.Mem()
	//@ requires offset == 0
	//@ requires len(buf_res) >= addr.IABytes + scmpRawInterfaceLen
	//@ requires buf === buf_res[:addr.IABytes+scmpRawInterfaceLen]
	//@ requires b != nil
	//@ requires acc(&i.IA)
	//@ requires b.Mem(buf_res)
	//@ ensures acc(&i.IA)
	//@ ensures b.Mem(buf_res)
	//@ decreases
	//@ outline (
	//@ b.ExchangePred(buf_res)
	//@ slices.SplitByIndex_Bytes(buf_res, 0, len(buf_res), addr.IABytes, writePerm)
	//@ unfold slices.AbsSlice_Bytes(buf_res, 0, addr.IABytes)
	binary.BigEndian.PutUint64(buf[offset:], uint64(i.IA))
	//@ fold slices.AbsSlice_Bytes(buf_res, 0, addr.IABytes)
	//@ slices.CombineAtIndex_Bytes(buf_res, 0, len(buf_res), addr.IABytes, writePerm)
	//@ apply slices.AbsSlice_Bytes(buf_res, 0, len(buf_res)) --* b.Mem(buf_res)
	//@ )
	offset += addr.IABytes
	//@ requires offset == addr.IABytes
	//@ requires len(buf_res) >= addr.IABytes + scmpRawInterfaceLen
	//@ requires buf === buf_res[:addr.IABytes+scmpRawInterfaceLen]
	//@ requires b != nil
	//@ requires acc(&i.IfID)
	//@ requires b.Mem(buf_res)
	//@ ensures acc(&i.IfID)
	//@ ensures b.Mem(buf_res)
	//@ decreases
	//@ outline (
	//@ b.ExchangePred(buf_res)
	//@ slices.SplitByIndex_Bytes(buf_res, 0, len(buf_res), addr.IABytes, writePerm)
	//@ slices.SplitByIndex_Bytes(buf_res, addr.IABytes, len(buf_res), addr.IABytes+scmpRawInterfaceLen, writePerm)
	//@ unfold slices.AbsSlice_Bytes(buf_res, addr.IABytes, addr.IABytes+scmpRawInterfaceLen)
	//@ assert forall i int :: 0 <= i && i < scmpRawInterfaceLen ==> &buf[offset:offset+scmpRawInterfaceLen][i] == &buf[offset + i]
	binary.BigEndian.PutUint64(buf[offset:offset+scmpRawInterfaceLen], i.IfID)
	//@ fold slices.AbsSlice_Bytes(buf_res, addr.IABytes, addr.IABytes+scmpRawInterfaceLen)
	//@ slices.CombineAtIndex_Bytes(buf_res, addr.IABytes, len(buf_res), addr.IABytes+scmpRawInterfaceLen, writePerm)
	//@ slices.CombineAtIndex_Bytes(buf_res, 0, len(buf_res), addr.IABytes, writePerm)
	//@ apply slices.AbsSlice_Bytes(buf_res, 0, len(buf_res)) --* b.Mem(buf_res)
	//@ )
	return nil/*@, buf_res@*/
}

//@ requires acc(gopacket.LayerTypesMem(), _)
//@ requires acc(&gopacket.LayerTypePayload, _)
//@ requires pb != nil
//@ requires pb.Mem()
//@ requires slices.AbsSlice_Bytes(data, 0, len(data))
//@ ensures err != nil ==> err.ErrorMem()
//@ decreases
func decodeSCMPExternalInterfaceDown(data []byte, pb gopacket.PacketBuilder) (err error) {
	s := &SCMPExternalInterfaceDown{}
	//@ fold slices.AbsSlice_Bytes(s.Contents, 0, len(s.Contents))
	//@ fold slices.AbsSlice_Bytes(s.Payload, 0, len(s.Payload))
	//@ fold s.BaseLayer.Mem()
	//@ fold s.Mem()
	err := s.DecodeFromBytes(data, pb)
	if err != nil {
		return err
	}
	pb.AddLayer(s)
	//@ fold gopacket.LayerTypePayload.Mem()
	return pb.NextDecoder(gopacket.LayerTypePayload)
}

// SCMPInternalConnectivityDown indicates the AS internal connection between 2
// routers is down. The format is as follows:
//
//   0                   1                   2                   3
//   0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
//  +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//  |              ISD              |                               |
//  +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+         AS                    +
//  |                                                               |
//  +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//  |                                                               |
//  +                   Ingress Interface ID                        +
//  |                                                               |
//  +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//  |                                                               |
//  +                   Egress Interface ID                         +
//  |                                                               |
//  +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//
type SCMPInternalConnectivityDown struct {
	BaseLayer
	
	IA      addr.IA
	Ingress uint64
	Egress  uint64
}

// LayerType returns LayerTypeSCMPInternalConnectivityDown.
//@ decreases
//@ pure
func (i *SCMPInternalConnectivityDown) LayerType() gopacket.LayerType {
	// (VerifiedSCION) TODO: replace with global
	return getLayerTypeSCMPInternalConnectivityDown()
}

// NextLayerType returns the layer type contained by this DecodingLayer.
//@ preserves acc(&gopacket.LayerTypePayload, _)
//@ decreases
func (*SCMPInternalConnectivityDown) NextLayerType() gopacket.LayerType {
	return gopacket.LayerTypePayload
}

// DecodeFromBytes decodes the given bytes into this layer.
//@ requires df != nil
//@ requires df.Mem()
//@ requires slices.AbsSlice_Bytes(data, 0, len(data))
//@ requires i.Mem()
//@ ensures i.Mem()
//@ ensures df.Mem()
//@ ensures res != nil ==> slices.AbsSlice_Bytes(data, 0, len(data))
//@ ensures res != nil ==> res.ErrorMem()
//@ decreases
func (i *SCMPInternalConnectivityDown) DecodeFromBytes(data []byte,
	df gopacket.DecodeFeedback) (res error) {

	minLength := addr.IABytes + 2*scmpRawInterfaceLen
	if size := len(data); size < minLength {
		df.SetTruncated()
		return serrors.New("buffer too short", "mininum_legth", minLength, "actual", size)
	}
	//@ unfold i.Mem()
	//@ defer fold i.Mem()
	offset := 0
	//@ requires offset == 0
	//@ requires acc(&i.IA)
	//@ requires len(data) >= addr.IABytes + 2*scmpRawInterfaceLen
	//@ requires slices.AbsSlice_Bytes(data, 0, len(data))
	//@ ensures slices.AbsSlice_Bytes(data, addr.IABytes, len(data))
	//@ ensures slices.AbsSlice_Bytes(data, 0, addr.IABytes)
	//@ ensures acc(&i.IA)
	//@ decreases
	//@ outline (
	//@ slices.SplitByIndex_Bytes(data, 0, len(data), addr.IABytes, writePerm)
	//@ unfold slices.AbsSlice_Bytes(data, 0, addr.IABytes)
	i.IA = addr.IA(binary.BigEndian.Uint64(data[offset:]))
	//@ fold slices.AbsSlice_Bytes(data, 0, addr.IABytes)
	//@ )
	offset += addr.IABytes
	//@ requires offset == addr.IABytes
	//@ requires acc(&i.Ingress)
	//@ requires len(data) >= addr.IABytes + 2*scmpRawInterfaceLen
	//@ requires slices.AbsSlice_Bytes(data, addr.IABytes, len(data))
	//@ ensures slices.AbsSlice_Bytes(data, addr.IABytes, addr.IABytes+scmpRawInterfaceLen)
	//@ ensures slices.AbsSlice_Bytes(data, addr.IABytes+scmpRawInterfaceLen, len(data))
	//@ ensures acc(&i.Ingress)
	//@ decreases
	//@ outline (
	//@ slices.SplitByIndex_Bytes(data, addr.IABytes, len(data), addr.IABytes+scmpRawInterfaceLen, writePerm)
	//@ unfold slices.AbsSlice_Bytes(data, addr.IABytes, addr.IABytes+scmpRawInterfaceLen)
	//@ assert forall i int :: 0 <= i && i < scmpRawInterfaceLen ==> &data[offset + i] == &data[offset : offset+scmpRawInterfaceLen][i]
	i.Ingress = binary.BigEndian.Uint64(data[offset : offset+scmpRawInterfaceLen])
	//@ fold slices.AbsSlice_Bytes(data, addr.IABytes, addr.IABytes+scmpRawInterfaceLen)
	//@ )
	offset += scmpRawInterfaceLen
	//@ requires offset == addr.IABytes + scmpRawInterfaceLen
	//@ requires acc(&i.Egress)
	//@ requires len(data) >= addr.IABytes + 2*scmpRawInterfaceLen
	//@ requires slices.AbsSlice_Bytes(data, addr.IABytes+scmpRawInterfaceLen, len(data))
	//@ ensures slices.AbsSlice_Bytes(data, addr.IABytes+scmpRawInterfaceLen, addr.IABytes+2*scmpRawInterfaceLen)
	//@ ensures slices.AbsSlice_Bytes(data, addr.IABytes+2*scmpRawInterfaceLen, len(data))
	//@ ensures acc(&i.Egress)
	//@ decreases
	//@ outline (
	//@ slices.SplitByIndex_Bytes(data, addr.IABytes+scmpRawInterfaceLen, len(data), addr.IABytes+2*scmpRawInterfaceLen, writePerm)
	//@ unfold slices.AbsSlice_Bytes(data, addr.IABytes+scmpRawInterfaceLen, addr.IABytes+2*scmpRawInterfaceLen)
	//@ assert forall i int :: 0 <= i && i < scmpRawInterfaceLen ==> &data[offset + i] == &data[offset : offset+scmpRawInterfaceLen][i]
	i.Egress = binary.BigEndian.Uint64(data[offset : offset+scmpRawInterfaceLen])
	//@ fold slices.AbsSlice_Bytes(data, addr.IABytes+scmpRawInterfaceLen, addr.IABytes+2*scmpRawInterfaceLen)
	//@ )
	offset += scmpRawInterfaceLen
	//@ requires offset == addr.IABytes + 2*scmpRawInterfaceLen
	//@ requires len(data) >= addr.IABytes + 2*scmpRawInterfaceLen
	//@ requires i.BaseLayer.Mem()
	//@ requires slices.AbsSlice_Bytes(data, 0, addr.IABytes)
	//@ requires slices.AbsSlice_Bytes(data, addr.IABytes, addr.IABytes+scmpRawInterfaceLen)
	//@ requires slices.AbsSlice_Bytes(data, addr.IABytes+scmpRawInterfaceLen, addr.IABytes+2*scmpRawInterfaceLen)
	//@ requires slices.AbsSlice_Bytes(data, addr.IABytes+2*scmpRawInterfaceLen, len(data))
	//@ ensures i.BaseLayer.Mem()
	//@ decreases
	//@ outline (
	//@ slices.CombineAtIndex_Bytes(data, 0, addr.IABytes+scmpRawInterfaceLen, addr.IABytes, writePerm)
	//@ slices.CombineAtIndex_Bytes(data, 0, addr.IABytes+2*scmpRawInterfaceLen, addr.IABytes+scmpRawInterfaceLen, writePerm)
	//@ unfold slices.AbsSlice_Bytes(data, 0, addr.IABytes+2*scmpRawInterfaceLen)
	//@ unfold slices.AbsSlice_Bytes(data, addr.IABytes+2*scmpRawInterfaceLen, len(data))
	//@ unfold i.BaseLayer.Mem()
	//@ assert forall i int :: offset <= i && i < len(data) ==> &data[offset:][i] == &data[offset + i]
	//@ assert forall l int :: offset <= l && l < len(data) ==> acc(&data[l])
	i.BaseLayer = BaseLayer{
		Contents: data[:offset],
		Payload:  data[offset:],
	}
	//@ assert forall l int :: 0 <= l && l < len(i.Payload) ==> &data[offset+l] == &i.Payload[l]
	//@ fold slices.AbsSlice_Bytes(i.Contents, 0, len(i.Contents))
	//@ fold slices.AbsSlice_Bytes(i.Payload, 0, len(i.Payload))
	//@ fold i.BaseLayer.Mem()
	//@ )
	return nil
}

// SerializeTo writes the serialized form of this layer into the
// SerializationBuffer, implementing gopacket.SerializableLayer.
//@ requires b != nil
//@ requires i.Mem()
//@ requires b.Mem(buf_init)
//@ ensures err == nil ==> buf_res != nil
//@ ensures err == nil ==> i.Mem() && b.Mem(buf_res)
//@ ensures err != nil ==> b.Mem(buf_init)
//@ ensures err != nil ==> err.ErrorMem()
//@ decreases
func (i *SCMPInternalConnectivityDown) SerializeTo(b gopacket.SerializeBuffer, opts gopacket.SerializeOptions/*@, ghost buf_init []byte @*/) (err error/*@, ghost buf_res []byte @*/) {

	buf, err/*@, buf_res@*/ := b.PrependBytes(addr.IABytes + 2*scmpRawInterfaceLen/*@, buf_init@*/)
	if err != nil {
		return err/*@, buf_res@*/
	}
	offset := 0
	//@ unfold i.Mem()
	//@ defer fold i.Mem()
	//@ requires offset == 0
	//@ requires len(buf_res) >= addr.IABytes + 2*scmpRawInterfaceLen
	//@ requires buf === buf_res[:addr.IABytes+2*scmpRawInterfaceLen]
	//@ requires b != nil
	//@ requires acc(&i.IA)
	//@ requires b.Mem(buf_res)
	//@ ensures acc(&i.IA)
	//@ ensures b.Mem(buf_res)
	//@ decreases
	//@ outline (
	//@ b.ExchangePred(buf_res)
	//@ slices.SplitByIndex_Bytes(buf_res, 0, len(buf_res), addr.IABytes, writePerm)
	//@ unfold slices.AbsSlice_Bytes(buf_res, 0, addr.IABytes)
	binary.BigEndian.PutUint64(buf[offset:], uint64(i.IA))
	//@ fold slices.AbsSlice_Bytes(buf_res, 0, addr.IABytes)
	//@ slices.CombineAtIndex_Bytes(buf_res, 0, len(buf_res), addr.IABytes, writePerm)
	//@ apply slices.AbsSlice_Bytes(buf_res, 0, len(buf_res)) --* b.Mem(buf_res)
	//@ )
	offset += addr.IABytes
	//@ requires offset == addr.IABytes
	//@ requires len(buf_res) >= addr.IABytes + 2*scmpRawInterfaceLen
	//@ requires buf === buf_res[:addr.IABytes+2*scmpRawInterfaceLen]
	//@ requires b != nil
	//@ requires acc(&i.Ingress)
	//@ requires b.Mem(buf_res)
	//@ ensures acc(&i.Ingress)
	//@ ensures b.Mem(buf_res)
	//@ decreases
	//@ outline (
	//@ b.ExchangePred(buf_res)
	//@ slices.SplitByIndex_Bytes(buf_res, 0, len(buf_res), addr.IABytes, writePerm)
	//@ slices.SplitByIndex_Bytes(buf_res, addr.IABytes, len(buf_res), addr.IABytes+scmpRawInterfaceLen, writePerm)
	//@ unfold slices.AbsSlice_Bytes(buf_res, addr.IABytes, addr.IABytes+scmpRawInterfaceLen)
	//@ assert forall i int :: 0 <= i && i < scmpRawInterfaceLen ==> &buf[offset:offset+scmpRawInterfaceLen][i] == &buf[offset + i]
	binary.BigEndian.PutUint64(buf[offset:offset+scmpRawInterfaceLen], i.Ingress)
	//@ fold slices.AbsSlice_Bytes(buf_res, addr.IABytes, addr.IABytes+scmpRawInterfaceLen)
	//@ slices.CombineAtIndex_Bytes(buf_res, addr.IABytes, len(buf_res), addr.IABytes+scmpRawInterfaceLen, writePerm)
	//@ slices.CombineAtIndex_Bytes(buf_res, 0, len(buf_res), addr.IABytes, writePerm)
	//@ apply slices.AbsSlice_Bytes(buf_res, 0, len(buf_res)) --* b.Mem(buf_res)
	//@ )
	offset += scmpRawInterfaceLen
	//@ requires offset == addr.IABytes+scmpRawInterfaceLen
	//@ requires len(buf_res) >= addr.IABytes + 2*scmpRawInterfaceLen
	//@ requires buf === buf_res[:addr.IABytes+2*scmpRawInterfaceLen]
	//@ requires b != nil
	//@ requires acc(&i.Egress)
	//@ requires b.Mem(buf_res)
	//@ ensures acc(&i.Egress)
	//@ ensures b.Mem(buf_res)
	//@ decreases
	//@ outline (
	//@ b.ExchangePred(buf_res)
	//@ slices.SplitByIndex_Bytes(buf_res, 0, len(buf_res), addr.IABytes+scmpRawInterfaceLen, writePerm)
	//@ slices.SplitByIndex_Bytes(buf_res, addr.IABytes+scmpRawInterfaceLen, len(buf_res), addr.IABytes+2*scmpRawInterfaceLen, writePerm)
	//@ unfold slices.AbsSlice_Bytes(buf_res, addr.IABytes+scmpRawInterfaceLen, addr.IABytes+2*scmpRawInterfaceLen)
	//@ assert forall i int :: 0 <= i && i < scmpRawInterfaceLen ==> &buf[offset:offset+scmpRawInterfaceLen][i] == &buf[offset + i]
	binary.BigEndian.PutUint64(buf[offset:offset+scmpRawInterfaceLen], i.Egress)
	//@ fold slices.AbsSlice_Bytes(buf_res, addr.IABytes+scmpRawInterfaceLen, addr.IABytes+2*scmpRawInterfaceLen)
	//@ slices.CombineAtIndex_Bytes(buf_res, addr.IABytes+scmpRawInterfaceLen, len(buf_res), addr.IABytes+2*scmpRawInterfaceLen, writePerm)
	//@ slices.CombineAtIndex_Bytes(buf_res, 0, len(buf_res), addr.IABytes+scmpRawInterfaceLen, writePerm)
	//@ apply slices.AbsSlice_Bytes(buf_res, 0, len(buf_res)) --* b.Mem(buf_res)
	//@ )
	return nil/*@, buf_res@*/
}

//@ requires acc(gopacket.LayerTypesMem(), _)
//@ requires acc(&gopacket.LayerTypePayload, _)
//@ requires pb != nil
//@ requires pb.Mem()
//@ requires slices.AbsSlice_Bytes(data, 0, len(data))
//@ ensures err != nil ==> err.ErrorMem()
//@ decreases
func decodeSCMPInternalConnectivityDown(data []byte, pb gopacket.PacketBuilder) (err error) {
	s := &SCMPInternalConnectivityDown{}
	//@ fold slices.AbsSlice_Bytes(s.Contents, 0, len(s.Contents))
	//@ fold slices.AbsSlice_Bytes(s.Payload, 0, len(s.Payload))
	//@ fold s.BaseLayer.Mem()
	//@ fold s.Mem()
	if err := s.DecodeFromBytes(data, pb); err != nil {
		return err
	}
	pb.AddLayer(s)
	// (VerifiedSCION): The following line needs a small refactor with a temporary variable
	//return pb.NextDecoder(s.NextLayerType())
	next := s.NextLayerType()
	//@ fold next.Mem()
	return pb.NextDecoder(next)
}

// SCMPEcho represents the structure of a ping.
//
//   0                   1                   2                   3
//   0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
//  +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//  |           Identifier          |        Sequence Number        |
//  +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//
type SCMPEcho struct {
	BaseLayer
	
	Identifier uint16
	SeqNumber  uint16
}

// LayerType returns LayerTypeSCMPEcho.
//@ decreases
//@ pure
func (i *SCMPEcho) LayerType() gopacket.LayerType {
	// (VerifiedSCION) TODO: replace with global
	return getLayerTypeSCMPEcho()
}

// NextLayerType returns the layer type contained by this DecodingLayer.
//@ preserves acc(&gopacket.LayerTypePayload, _)
//@ decreases
func (*SCMPEcho) NextLayerType() gopacket.LayerType {
	return gopacket.LayerTypePayload
}

// DecodeFromBytes decodes the given bytes into this layer.
//@ requires df != nil
//@ requires df.Mem()
//@ requires slices.AbsSlice_Bytes(data, 0, len(data))
//@ requires i.Mem()
//@ ensures i.Mem()
//@ ensures df.Mem()
//@ ensures res != nil ==> slices.AbsSlice_Bytes(data, 0, len(data))
//@ ensures res != nil ==> res.ErrorMem()
//@ decreases
func (i *SCMPEcho) DecodeFromBytes(data []byte, df gopacket.DecodeFeedback) (res error) {
	minLength := 4
	if size := len(data); size < minLength {
		df.SetTruncated()
		return serrors.New("buffer too short", "min", minLength, "actual", size)
	}
	//@ unfold i.Mem()
	//@ defer fold i.Mem()
	offset := 0
	//@ requires offset == 0
	//@ requires acc(&i.Identifier)
	//@ requires len(data) >= 4
	//@ requires slices.AbsSlice_Bytes(data, 0, len(data))
	//@ ensures slices.AbsSlice_Bytes(data, 2, len(data))
	//@ ensures slices.AbsSlice_Bytes(data, 0, 2)
	//@ ensures acc(&i.Identifier)
	//@ decreases
	//@ outline (
	//@ slices.SplitByIndex_Bytes(data, 0, len(data), 2, writePerm)
	//@ unfold slices.AbsSlice_Bytes(data, 0, 2)
	i.Identifier = binary.BigEndian.Uint16(data[:2])
	//@ fold slices.AbsSlice_Bytes(data, 0, 2)
	//@ )
	offset += 2
	//@ requires offset == 2
	//@ requires acc(&i.SeqNumber)
	//@ requires len(data) >= 4
	//@ requires slices.AbsSlice_Bytes(data, 2, len(data))
	//@ ensures slices.AbsSlice_Bytes(data, 2, 4)
	//@ ensures slices.AbsSlice_Bytes(data, 4, len(data))
	//@ ensures acc(&i.SeqNumber)
	//@ decreases
	//@ outline (
	//@ slices.SplitByIndex_Bytes(data, 2, len(data), 4, writePerm)
	//@ unfold slices.AbsSlice_Bytes(data, 2, 4)
	//@ assert forall i int :: 0 <= i && i < 2 ==> &data[offset + i] == &data[offset : offset+2][i]
	i.SeqNumber = binary.BigEndian.Uint16(data[offset : offset+2])
	//@ fold slices.AbsSlice_Bytes(data, 2, 4)
	//@ )
	offset += 2
	//@ requires offset == 4
	//@ requires len(data) >= 4
	//@ requires i.BaseLayer.Mem()
	//@ requires slices.AbsSlice_Bytes(data, 0, 2)
	//@ requires slices.AbsSlice_Bytes(data, 2, 4)
	//@ requires slices.AbsSlice_Bytes(data, 4, len(data))
	//@ ensures i.BaseLayer.Mem()
	//@ decreases
	//@ outline (
	//@ slices.CombineAtIndex_Bytes(data, 0, 4, 2, writePerm)
	//@ unfold slices.AbsSlice_Bytes(data, 0, 4)
	//@ unfold slices.AbsSlice_Bytes(data, 4, len(data))
	//@ unfold i.BaseLayer.Mem()
	//@ assert forall i int :: offset <= i && i < len(data) ==> &data[offset:][i] == &data[offset + i]
	i.BaseLayer = BaseLayer{
		Contents: data[:offset],
		Payload:  data[offset:],
	}
	//@ assert forall l int :: 0 <= l && l < len(i.Payload) ==> &data[offset+l] == &i.Payload[l]
	//@ fold slices.AbsSlice_Bytes(i.Contents, 0, len(i.Contents))
	//@ fold slices.AbsSlice_Bytes(i.Payload, 0, len(i.Payload))
	//@ fold i.BaseLayer.Mem()
	//@ )
	return nil
}

// SerializeTo writes the serialized form of this layer into the
// SerializationBuffer, implementing gopacket.SerializableLayer.
//@ requires b != nil
//@ requires i.Mem()
//@ requires b.Mem(buf_init)
//@ ensures err == nil ==> buf_res != nil
//@ ensures err == nil ==> i.Mem() && b.Mem(buf_res)
//@ ensures err != nil ==> b.Mem(buf_init)
//@ ensures err != nil ==> err.ErrorMem()
//@ decreases
func (i *SCMPEcho) SerializeTo(b gopacket.SerializeBuffer, opts gopacket.SerializeOptions/*@, ghost buf_init []byte @*/) (err error/*@, ghost buf_res []byte @*/) {
	buf, err/*@, buf_res@*/ := b.PrependBytes(4/*@, buf_init@*/)
	if err != nil {
		return err/*@, buf_res@*/
	}
	offset := 0
	//@ unfold i.Mem()
	//@ defer fold i.Mem()
	//@ requires offset == 0
	//@ requires len(buf_res) >= 4
	//@ requires buf === buf_res[:4]
	//@ requires b != nil
	//@ requires acc(&i.Identifier)
	//@ requires b.Mem(buf_res)
	//@ ensures acc(&i.Identifier)
	//@ ensures b.Mem(buf_res)
	//@ decreases
	//@ outline (
	//@ b.ExchangePred(buf_res)
	//@ slices.SplitByIndex_Bytes(buf_res, 0, len(buf_res), 2, writePerm)
	//@ unfold slices.AbsSlice_Bytes(buf_res, 0, 2)
	binary.BigEndian.PutUint16(buf[:2], i.Identifier)
	//@ fold slices.AbsSlice_Bytes(buf_res, 0, 2)
	//@ slices.CombineAtIndex_Bytes(buf_res, 0, len(buf_res), 2, writePerm)
	//@ apply slices.AbsSlice_Bytes(buf_res, 0, len(buf_res)) --* b.Mem(buf_res)
	//@ )
	offset += 2
	//@ requires offset == 2
	//@ requires len(buf_res) >= 4
	//@ requires buf === buf_res[:4]
	//@ requires b != nil
	//@ requires acc(&i.SeqNumber)
	//@ requires b.Mem(buf_res)
	//@ ensures acc(&i.SeqNumber)
	//@ ensures b.Mem(buf_res)
	//@ decreases
	//@ outline (
	//@ b.ExchangePred(buf_res)
	//@ slices.SplitByIndex_Bytes(buf_res, 0, len(buf_res), 2, writePerm)
	//@ slices.SplitByIndex_Bytes(buf_res, 2, len(buf_res), 4, writePerm)
	//@ unfold slices.AbsSlice_Bytes(buf_res, 2, 4)
	//@ assert forall i int :: 0 <= i && i < 2 ==> &buf[offset:offset+2][i] == &buf[offset + i]
	binary.BigEndian.PutUint16(buf[offset:offset+2], i.SeqNumber)
	//@ fold slices.AbsSlice_Bytes(buf_res, 2, 4)
	//@ slices.CombineAtIndex_Bytes(buf_res, 2, len(buf_res), 4, writePerm)
	//@ slices.CombineAtIndex_Bytes(buf_res, 0, len(buf_res), 2, writePerm)
	//@ apply slices.AbsSlice_Bytes(buf_res, 0, len(buf_res)) --* b.Mem(buf_res)
	//@ )
	return nil/*@, buf_res@*/
}

//@ requires acc(gopacket.LayerTypesMem(), _)
//@ requires acc(&gopacket.LayerTypePayload, _)
//@ requires pb != nil
//@ requires pb.Mem()
//@ requires slices.AbsSlice_Bytes(data, 0, len(data))
//@ ensures err != nil ==> err.ErrorMem()
//@ decreases
func decodeSCMPEcho(data []byte, pb gopacket.PacketBuilder) (err error) {
	s := &SCMPEcho{}
	//@ fold slices.AbsSlice_Bytes(s.Contents, 0, len(s.Contents))
	//@ fold slices.AbsSlice_Bytes(s.Payload, 0, len(s.Payload))
	//@ fold s.BaseLayer.Mem()
	//@ fold s.Mem()
	if err := s.DecodeFromBytes(data, pb); err != nil {
		return err
	}
	pb.AddLayer(s)
	// (VerifiedSCION): The following line needs a small refactor with a temporary variable
	//return pb.NextDecoder(s.NextLayerType())
	next := s.NextLayerType()
	//@ fold next.Mem()
	return pb.NextDecoder(next)
}

// SCMPParameterProblem represents the structure of a parameter problem message.
//
//  +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//  |            reserved           |           Pointer             |
//  +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//
type SCMPParameterProblem struct {
	BaseLayer
	
	Pointer uint16
}

// LayerType returns LayerTypeSCMPParameterProblem.
//@ decreases
//@ pure
func (i *SCMPParameterProblem) LayerType() gopacket.LayerType {
	// (VerifiedSCION) TODO: replace with global
	return getLayerTypeSCMPParameterProblem()
}

// NextLayerType returns the layer type contained by this DecodingLayer.
//@ preserves acc(&gopacket.LayerTypePayload, _)
//@ decreases
func (*SCMPParameterProblem) NextLayerType() gopacket.LayerType {
	return gopacket.LayerTypePayload
}

// DecodeFromBytes decodes the given bytes into this layer.
//@ requires df != nil
//@ requires df.Mem()
//@ requires slices.AbsSlice_Bytes(data, 0, len(data))
//@ requires i.Mem()
//@ ensures i.Mem()
//@ ensures df.Mem()
//@ ensures res != nil ==> slices.AbsSlice_Bytes(data, 0, len(data))
//@ ensures res != nil ==> res.ErrorMem()
//@ decreases
func (i *SCMPParameterProblem) DecodeFromBytes(data []byte, df gopacket.DecodeFeedback) (res error) {
	minLength := 2 + 2
	if size := len(data); size < minLength {
		df.SetTruncated()
		return serrors.New("buffer too short", "min", minLength, "actual", size)
	}
	//@ unfold i.Mem()
	//@ defer fold i.Mem()
	//@ requires acc(&i.Pointer)
	//@ requires len(data) >= 4
	//@ preserves slices.AbsSlice_Bytes(data, 0, len(data))
	//@ ensures acc(&i.Pointer)
	//@ decreases
	//@ outline (
	//@ slices.SplitByIndex_Bytes(data, 0, len(data), 2, writePerm)
	//@ slices.SplitByIndex_Bytes(data, 2, len(data), 4, writePerm)
	//@ unfold slices.AbsSlice_Bytes(data, 2, 4)
	//@ assert forall i int :: 0 <= i && i < 2 ==> &data[2:4][i] == &data[2 + i]
	i.Pointer = binary.BigEndian.Uint16(data[2:4])
	//@ fold slices.AbsSlice_Bytes(data, 2, 4)
	//@ slices.CombineAtIndex_Bytes(data, 0, 4, 2, writePerm)
	//@ slices.CombineAtIndex_Bytes(data, 0, len(data), 4, writePerm)
	//@ )
	//@ requires len(data) >= 4
	//@ requires i.BaseLayer.Mem()
	//@ requires slices.AbsSlice_Bytes(data, 0, len(data))
	//@ ensures i.BaseLayer.Mem()
	//@ decreases
	//@ outline (
	//@ unfold slices.AbsSlice_Bytes(data, 0, len(data))
	//@ unfold i.BaseLayer.Mem()
	//@ assert forall i int :: 0 <= i && i < len(data) ==> &data[4:][i] == &data[4 + i]
	i.BaseLayer = BaseLayer{
		Contents: data[:4],
		Payload:  data[4:],
	}
	//@ assert forall l int :: 0 <= l && l < len(i.Payload) ==> &data[4+l] == &i.Payload[l]
	//@ fold slices.AbsSlice_Bytes(i.Contents, 0, len(i.Contents))
	//@ fold slices.AbsSlice_Bytes(i.Payload, 0, len(i.Payload))
	//@ fold i.BaseLayer.Mem()
	//@ )
	return nil
}

// SerializeTo writes the serialized form of this layer into the
// SerializationBuffer, implementing gopacket.SerializableLayer.
//@ requires b != nil
//@ requires i.Mem()
//@ requires b.Mem(buf_init)
//@ ensures err == nil ==> buf_res != nil
//@ ensures err == nil ==> i.Mem() && b.Mem(buf_res)
//@ ensures err != nil ==> b.Mem(buf_init)
//@ ensures err != nil ==> err.ErrorMem()
//@ decreases
func (i *SCMPParameterProblem) SerializeTo(b gopacket.SerializeBuffer, opts gopacket.SerializeOptions/*@, ghost buf_init []byte @*/) (err error/*@, ghost buf_res []byte @*/) {

	buf, err/*@, buf_res@*/ := b.PrependBytes(2 + 2/*@, buf_init@*/)
	if err != nil {
		return err/*@, buf_res@*/
	}
	//@ unfold i.Mem()
	//@ defer fold i.Mem()
	//@ requires len(buf_res) >= 4
	//@ requires buf === buf_res[:4]
	//@ requires b != nil
	//@ preserves b.Mem(buf_res)
	//@ decreases
	//@ outline (
	//@ b.ExchangePred(buf_res)
	//@ slices.SplitByIndex_Bytes(buf_res, 0, len(buf_res), 2, writePerm)
	//@ unfold slices.AbsSlice_Bytes(buf_res, 0, 2)
	binary.BigEndian.PutUint16(buf[0:2], uint16(0)) //Reserved
	//@ fold slices.AbsSlice_Bytes(buf_res, 0, 2)
	//@ slices.CombineAtIndex_Bytes(buf_res, 0, len(buf_res), 2, writePerm)
	//@ apply slices.AbsSlice_Bytes(buf_res, 0, len(buf_res)) --* b.Mem(buf_res)
	//@ )
	//@ requires len(buf_res) >= 4
	//@ requires buf === buf_res[:4]
	//@ requires b != nil
	//@ requires acc(&i.Pointer)
	//@ requires b.Mem(buf_res)
	//@ ensures acc(&i.Pointer)
	//@ ensures b.Mem(buf_res)
	//@ decreases
	//@ outline (
	//@ b.ExchangePred(buf_res)
	//@ slices.SplitByIndex_Bytes(buf_res, 0, len(buf_res), 2, writePerm)
	//@ slices.SplitByIndex_Bytes(buf_res, 2, len(buf_res), 4, writePerm)
	//@ unfold slices.AbsSlice_Bytes(buf_res, 2, 4)
	//@ assert forall i int :: 0 <= i && i < 2 ==> &buf[2:4][i] == &buf[2 + i]
	binary.BigEndian.PutUint16(buf[2:4], i.Pointer)
	//@ fold slices.AbsSlice_Bytes(buf_res, 2, 4)
	//@ slices.CombineAtIndex_Bytes(buf_res, 2, len(buf_res), 4, writePerm)
	//@ slices.CombineAtIndex_Bytes(buf_res, 0, len(buf_res), 2, writePerm)
	//@ apply slices.AbsSlice_Bytes(buf_res, 0, len(buf_res)) --* b.Mem(buf_res)
	//@ )
	return nil/*@, buf_res@*/
}

//@ requires acc(gopacket.LayerTypesMem(), _)
//@ requires acc(&gopacket.LayerTypePayload, _)
//@ requires pb != nil
//@ requires pb.Mem()
//@ requires slices.AbsSlice_Bytes(data, 0, len(data))
//@ ensures err != nil ==> err.ErrorMem()
//@ decreases
func decodeSCMPParameterProblem(data []byte, pb gopacket.PacketBuilder) (err error) {
	s := &SCMPParameterProblem{}
	//@ fold slices.AbsSlice_Bytes(s.Contents, 0, len(s.Contents))
	//@ fold slices.AbsSlice_Bytes(s.Payload, 0, len(s.Payload))
	//@ fold s.BaseLayer.Mem()
	//@ fold s.Mem()
	if err := s.DecodeFromBytes(data, pb); err != nil {
		return err
	}
	pb.AddLayer(s)
	// (VerifiedSCION): The following line needs a small refactor with a temporary variable
	//return pb.NextDecoder(s.NextLayerType())
	next := s.NextLayerType()
	//@ fold next.Mem()
	return pb.NextDecoder(next)
}

// SCMPTraceroute represents the structure of a traceroute.
//
//   0                   1                   2                   3
//   0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
//  +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//  |           Identifier          |        Sequence Number        |
//  +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//  |              ISD              |                               |
//  +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+         AS                    +
//  |                                                               |
//  +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//  |                                                               |
//  +                        Interface ID                           +
//  |                                                               |
//  +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//
type SCMPTraceroute struct {
	BaseLayer
	
	Identifier uint16
	Sequence   uint16
	IA         addr.IA
	Interface  uint64
}

// LayerType returns LayerTypeSCMPTraceroute.
//@ decreases
//@ pure
func (i *SCMPTraceroute) LayerType() gopacket.LayerType {
	// (VerifiedSCION) TODO: replace with global
	return getLayerTypeSCMPTraceroute()
}

// NextLayerType returns the layer type contained by this DecodingLayer.
//@ preserves acc(&gopacket.LayerTypePayload, _)
//@ decreases
func (*SCMPTraceroute) NextLayerType() gopacket.LayerType {
	return gopacket.LayerTypePayload
}

// DecodeFromBytes decodes the given bytes into this layer.
//@ requires df != nil
//@ requires df.Mem()
//@ requires slices.AbsSlice_Bytes(data, 0, len(data))
//@ requires i.Mem()
//@ ensures i.Mem()
//@ ensures df.Mem()
//@ ensures res != nil ==> slices.AbsSlice_Bytes(data, 0, len(data))
//@ ensures res != nil ==> res.ErrorMem()
//@ decreases
func (i *SCMPTraceroute) DecodeFromBytes(data []byte, df gopacket.DecodeFeedback) (res error) {
	minLength := 2 + 2 + addr.IABytes + scmpRawInterfaceLen
	if size := len(data); size < minLength {
		df.SetTruncated()
		return serrors.New("buffer too short", "min", minLength, "actual", size)
	}
	//@ unfold i.Mem()
	//@ defer fold i.Mem()
	offset := 0
	//@ requires offset == 0
	//@ requires acc(&i.Identifier)
	//@ requires len(data) >= 2 + 2 + addr.IABytes + scmpRawInterfaceLen
	//@ requires slices.AbsSlice_Bytes(data, 0, len(data))
	//@ ensures slices.AbsSlice_Bytes(data, 0, 2)
	//@ ensures slices.AbsSlice_Bytes(data, 2, len(data))
	//@ ensures acc(&i.Identifier)
	//@ decreases
	//@ outline (
	//@ slices.SplitByIndex_Bytes(data, 0, len(data), 2, writePerm)
	//@ unfold slices.AbsSlice_Bytes(data, 0, 2)
	i.Identifier = binary.BigEndian.Uint16(data[offset : offset+2])
	//@ fold slices.AbsSlice_Bytes(data, 0, 2)
	//@ )
	offset += 2
	//@ requires offset == 2
	//@ requires acc(&i.Sequence)
	//@ requires len(data) >= 2 + 2 + addr.IABytes + scmpRawInterfaceLen
	//@ requires slices.AbsSlice_Bytes(data, 2, len(data))
	//@ ensures slices.AbsSlice_Bytes(data, 2, 2+2)
	//@ ensures slices.AbsSlice_Bytes(data, 2+2, len(data))
	//@ ensures acc(&i.Sequence)
	//@ decreases
	//@ outline (
	//@ slices.SplitByIndex_Bytes(data, 2, len(data), 2+2, writePerm)
	//@ unfold slices.AbsSlice_Bytes(data, 2, 2+2)
	//@ assert forall i int :: 0 <= i && i < 2 ==> &data[offset + i] == &data[offset : offset+2][i]
	i.Sequence = binary.BigEndian.Uint16(data[offset : offset+2])
	//@ fold slices.AbsSlice_Bytes(data, 2, 2+2)
	//@ )
	offset += 2
	//@ requires offset == 2 + 2
	//@ requires acc(&i.IA)
	//@ requires len(data) >= 2 + 2 + addr.IABytes + scmpRawInterfaceLen
	//@ requires slices.AbsSlice_Bytes(data, 2+2, len(data))
	//@ ensures slices.AbsSlice_Bytes(data, 2+2, 2+2+addr.IABytes)
	//@ ensures slices.AbsSlice_Bytes(data, 2+2+addr.IABytes, len(data))
	//@ ensures acc(&i.IA)
	//@ decreases
	//@ outline (
	//@ slices.SplitByIndex_Bytes(data, 2+2, len(data), 2+2+addr.IABytes, writePerm)
	//@ unfold slices.AbsSlice_Bytes(data, 2+2, 2+2+addr.IABytes)
	//@ assert forall i int :: 0 <= i && i < addr.IABytes ==> &data[offset + i] == &data[offset : offset+addr.IABytes][i]
	i.IA = addr.IA(binary.BigEndian.Uint64(data[offset : offset+addr.IABytes]))
	//@ fold slices.AbsSlice_Bytes(data, 2+2, 2+2+addr.IABytes)
	//@ )
	offset += addr.IABytes
	//@ requires offset == 2 + 2 + addr.IABytes
	//@ requires acc(&i.Interface)
	//@ requires len(data) >= 2 + 2 + addr.IABytes + scmpRawInterfaceLen
	//@ requires slices.AbsSlice_Bytes(data, 2+2+addr.IABytes, len(data))
	//@ ensures slices.AbsSlice_Bytes(data, 2+2+addr.IABytes, 2+2+addr.IABytes+scmpRawInterfaceLen)
	//@ ensures slices.AbsSlice_Bytes(data, 2+2+addr.IABytes+scmpRawInterfaceLen, len(data))
	//@ ensures acc(&i.Interface)
	//@ decreases
	//@ outline (
	//@ slices.SplitByIndex_Bytes(data, 2+2+addr.IABytes, len(data), 2+2+addr.IABytes+scmpRawInterfaceLen, writePerm)
	//@ unfold slices.AbsSlice_Bytes(data, 2+2+addr.IABytes, 2+2+addr.IABytes+scmpRawInterfaceLen)
	//@ assert forall i int :: 0 <= i && i < scmpRawInterfaceLen ==> &data[offset + i] == &data[offset : offset+addr.IABytes][i]
	i.Interface = binary.BigEndian.Uint64(data[offset : offset+scmpRawInterfaceLen])
	//@ fold slices.AbsSlice_Bytes(data, 2+2+addr.IABytes, 2+2+addr.IABytes+scmpRawInterfaceLen)
	//@ )
	offset += scmpRawInterfaceLen
	//@ requires offset == 2 + 2 + addr.IABytes + scmpRawInterfaceLen
	//@ requires len(data) >= 2 + 2 + addr.IABytes + scmpRawInterfaceLen
	//@ requires i.BaseLayer.Mem()
	//@ requires slices.AbsSlice_Bytes(data, 0, 2)
	//@ requires slices.AbsSlice_Bytes(data, 2, 2+2)
	//@ requires slices.AbsSlice_Bytes(data, 2+2, 2+2+addr.IABytes)
	//@ requires slices.AbsSlice_Bytes(data, 2+2+addr.IABytes, 2+2+addr.IABytes+scmpRawInterfaceLen)
	//@ requires slices.AbsSlice_Bytes(data, 2+2+addr.IABytes+scmpRawInterfaceLen, len(data))
	//@ ensures i.BaseLayer.Mem()
	//@ decreases
	//@ outline (
	//@ slices.CombineAtIndex_Bytes(data, 0, 2+2, 2, writePerm)
	//@ slices.CombineAtIndex_Bytes(data, 0, 2+2+addr.IABytes, 2+2, writePerm)
	//@ slices.CombineAtIndex_Bytes(data, 0, 2+2+addr.IABytes+scmpRawInterfaceLen, 2+2+addr.IABytes, writePerm)
	//@ unfold slices.AbsSlice_Bytes(data, 0, 2+2+addr.IABytes+scmpRawInterfaceLen)
	//@ unfold slices.AbsSlice_Bytes(data, 2+2+addr.IABytes+scmpRawInterfaceLen, len(data))
	//@ unfold i.BaseLayer.Mem()
	//@ assert forall i int :: offset <= i && i < len(data) ==> &data[offset:][i] == &data[offset + i]
	//@ assert forall l int :: offset <= l && l < len(data) ==> acc(&data[l])
	i.BaseLayer = BaseLayer{
		Contents: data[:offset],
		Payload:  data[offset:],
	}
	//@ assert forall l int :: 0 <= l && l < len(i.Payload) ==> &data[offset+l] == &i.Payload[l]
	//@ fold slices.AbsSlice_Bytes(i.Contents, 0, len(i.Contents))
	//@ fold slices.AbsSlice_Bytes(i.Payload, 0, len(i.Payload))
	//@ fold i.BaseLayer.Mem()
	//@ )
	return nil
}

// SerializeTo writes the serialized form of this layer into the
// SerializationBuffer, implementing gopacket.SerializableLayer.
//@ requires b != nil
//@ requires i.Mem()
//@ requires b.Mem(buf_init)
//@ ensures err == nil ==> buf_res != nil
//@ ensures err == nil ==> i.Mem() && b.Mem(buf_res)
//@ ensures err != nil ==> b.Mem(buf_init)
//@ ensures err != nil ==> err.ErrorMem()
//@ decreases
func (i *SCMPTraceroute) SerializeTo(b gopacket.SerializeBuffer, opts gopacket.SerializeOptions/*@, ghost buf_init []byte @*/) (err error/*@, ghost buf_res []byte @*/) {

	buf, err/*@, buf_res@*/ := b.PrependBytes(2 + 2 + addr.IABytes + scmpRawInterfaceLen/*@, buf_init@*/)
	if err != nil {
		return err/*@, buf_res@*/
	}
	offset := 0
	//@ unfold i.Mem()
	//@ defer fold i.Mem()
	//@ requires offset == 0
	//@ requires len(buf_res) >= 2 + 2 + addr.IABytes + scmpRawInterfaceLen
	//@ requires buf === buf_res[:2+2+addr.IABytes+scmpRawInterfaceLen]
	//@ requires b != nil
	//@ requires acc(&i.Identifier)
	//@ requires b.Mem(buf_res)
	//@ ensures acc(&i.Identifier)
	//@ ensures b.Mem(buf_res)
	//@ decreases
	//@ outline (
	//@ b.ExchangePred(buf_res)
	//@ slices.SplitByIndex_Bytes(buf_res, 0, len(buf_res), 2, writePerm)
	//@ unfold slices.AbsSlice_Bytes(buf_res, 0, 2)
	binary.BigEndian.PutUint16(buf[:2], i.Identifier)
	//@ fold slices.AbsSlice_Bytes(buf_res, 0, 2)
	//@ slices.CombineAtIndex_Bytes(buf_res, 0, len(buf_res), 2, writePerm)
	//@ apply slices.AbsSlice_Bytes(buf_res, 0, len(buf_res)) --* b.Mem(buf_res)
	//@ )
	offset += 2
	//@ requires offset == 2
	//@ requires len(buf_res) >= 2 + 2 + addr.IABytes + scmpRawInterfaceLen
	//@ requires buf === buf_res[:2 + 2 + addr.IABytes + scmpRawInterfaceLen]
	//@ requires b != nil
	//@ requires acc(&i.Sequence)
	//@ requires b.Mem(buf_res)
	//@ ensures acc(&i.Sequence)
	//@ ensures b.Mem(buf_res)
	//@ decreases
	//@ outline (
	//@ b.ExchangePred(buf_res)
	//@ slices.SplitByIndex_Bytes(buf_res, 0, len(buf_res), 2, writePerm)
	//@ slices.SplitByIndex_Bytes(buf_res, 2, len(buf_res), 2+2, writePerm)
	//@ unfold slices.AbsSlice_Bytes(buf_res, 2, 2+2)
	//@ assert forall i int :: 0 <= i && i < 2 ==> &buf[offset:offset+2][i] == &buf[offset + i]
	binary.BigEndian.PutUint16(buf[offset:offset+2], i.Sequence)
	//@ fold slices.AbsSlice_Bytes(buf_res, 2, 2+2)
	//@ slices.CombineAtIndex_Bytes(buf_res, 2, len(buf_res), 2+2, writePerm)
	//@ slices.CombineAtIndex_Bytes(buf_res, 0, len(buf_res), 2, writePerm)
	//@ apply slices.AbsSlice_Bytes(buf_res, 0, len(buf_res)) --* b.Mem(buf_res)
	//@ )
	offset += 2
	//@ requires offset == 2 + 2
	//@ requires len(buf_res) >= 2 + 2 + addr.IABytes + scmpRawInterfaceLen
	//@ requires buf === buf_res[:2 + 2 + addr.IABytes + scmpRawInterfaceLen]
	//@ requires b != nil
	//@ requires acc(&i.IA)
	//@ requires b.Mem(buf_res)
	//@ ensures acc(&i.IA)
	//@ ensures b.Mem(buf_res)
	//@ decreases
	//@ outline (
	//@ b.ExchangePred(buf_res)
	//@ slices.SplitByIndex_Bytes(buf_res, 0, len(buf_res), 2+2, writePerm)
	//@ slices.SplitByIndex_Bytes(buf_res, 2+2, len(buf_res), 2+2+addr.IABytes, writePerm)
	//@ unfold slices.AbsSlice_Bytes(buf_res, 2+2, 2+2+addr.IABytes)
	//@ assert forall i int :: 0 <= i && i < addr.IABytes ==> &buf[offset:offset+addr.IABytes][i] == &buf[offset + i]
	binary.BigEndian.PutUint64(buf[offset:offset+addr.IABytes], uint64(i.IA))
	//@ fold slices.AbsSlice_Bytes(buf_res, 2+2, 2+2+addr.IABytes)
	//@ slices.CombineAtIndex_Bytes(buf_res, 2+2, len(buf_res), 2+2+addr.IABytes, writePerm)
	//@ slices.CombineAtIndex_Bytes(buf_res, 0, len(buf_res), 2+2, writePerm)
	//@ apply slices.AbsSlice_Bytes(buf_res, 0, len(buf_res)) --* b.Mem(buf_res)
	//@ )
	offset += addr.IABytes
	//@ requires offset == 2 + 2 + addr.IABytes
	//@ requires len(buf_res) >= 2 + 2 + addr.IABytes + scmpRawInterfaceLen
	//@ requires buf === buf_res[:2 + 2 + addr.IABytes + scmpRawInterfaceLen]
	//@ requires b != nil
	//@ requires acc(&i.Interface)
	//@ requires b.Mem(buf_res)
	//@ ensures acc(&i.Interface)
	//@ ensures b.Mem(buf_res)
	//@ decreases
	//@ outline (
	//@ b.ExchangePred(buf_res)
	//@ slices.SplitByIndex_Bytes(buf_res, 0, len(buf_res), 2+2+addr.IABytes, writePerm)
	//@ slices.SplitByIndex_Bytes(buf_res, 2+2+addr.IABytes, len(buf_res), 2+2+addr.IABytes+scmpRawInterfaceLen, writePerm)
	//@ unfold slices.AbsSlice_Bytes(buf_res, 2+2+addr.IABytes, 2+2+addr.IABytes+scmpRawInterfaceLen)
	//@ assert forall i int :: 0 <= i && i < scmpRawInterfaceLen ==> &buf[offset:offset+scmpRawInterfaceLen][i] == &buf[offset + i]
	binary.BigEndian.PutUint64(buf[offset:offset+scmpRawInterfaceLen], i.Interface)
	//@ fold slices.AbsSlice_Bytes(buf_res, 2+2+addr.IABytes, 2+2+addr.IABytes+scmpRawInterfaceLen)
	//@ slices.CombineAtIndex_Bytes(buf_res, 2+2+addr.IABytes, len(buf_res), 2+2+addr.IABytes+scmpRawInterfaceLen, writePerm)
	//@ slices.CombineAtIndex_Bytes(buf_res, 0, len(buf_res), 2+2+addr.IABytes, writePerm)
	//@ apply slices.AbsSlice_Bytes(buf_res, 0, len(buf_res)) --* b.Mem(buf_res)
	//@ )
	return nil/*@, buf_res@*/
}

//@ requires acc(gopacket.LayerTypesMem(), _)
//@ requires acc(&gopacket.LayerTypePayload, _)
//@ requires pb != nil
//@ requires pb.Mem()
//@ requires slices.AbsSlice_Bytes(data, 0, len(data))
//@ ensures err != nil ==> err.ErrorMem()
//@ decreases
func decodeSCMPTraceroute(data []byte, pb gopacket.PacketBuilder) (err error) {
	s := &SCMPTraceroute{}
	//@ fold slices.AbsSlice_Bytes(s.Contents, 0, len(s.Contents))
	//@ fold slices.AbsSlice_Bytes(s.Payload, 0, len(s.Payload))
	//@ fold s.BaseLayer.Mem()
	//@ fold s.Mem()
	if err := s.DecodeFromBytes(data, pb); err != nil {
		return err
	}
	pb.AddLayer(s)
	// (VerifiedSCION): The following line needs a small refactor with a temporary variable
	//return pb.NextDecoder(s.NextLayerType())
	next := s.NextLayerType()
	//@ fold next.Mem()
	return pb.NextDecoder(next)
}

// SCMPDestinationUnreachable represents the structure of a destination
// unreachable message.
//
//   0                   1                   2                   3
//   0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
//  +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//  |                             Unused                            |
//  +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
type SCMPDestinationUnreachable struct {
	BaseLayer
}

// LayerType returns LayerTypeSCMPTraceroute.
//@ decreases
//@ pure
func (i *SCMPDestinationUnreachable) LayerType() gopacket.LayerType {
	// (VerifiedSCION) TODO: replace with global
	return getLayerTypeSCMPDestinationUnreachable()
}

// NextLayerType returns the layer type contained by this DecodingLayer.
//@ preserves acc(&gopacket.LayerTypePayload, _)
//@ decreases
func (*SCMPDestinationUnreachable) NextLayerType() gopacket.LayerType {
	return gopacket.LayerTypePayload
}

// DecodeFromBytes decodes the given bytes into this layer.
//@ requires df != nil
//@ requires df.Mem()
//@ requires slices.AbsSlice_Bytes(data, 0, len(data))
//@ requires i.Mem()
//@ ensures i.Mem()
//@ ensures df.Mem()
//@ ensures res != nil ==> slices.AbsSlice_Bytes(data, 0, len(data))
//@ ensures res != nil ==> res.ErrorMem()
//@ decreases
func (i *SCMPDestinationUnreachable) DecodeFromBytes(data []byte,
	df gopacket.DecodeFeedback) (res error) {

	minLength := 4
	if size := len(data); size < minLength {
		df.SetTruncated()
		return serrors.New("buffer too short", "min", minLength, "actual", size)
	}
	//@ unfold i.Mem()
	//@ defer fold i.Mem()
	//@ unfold i.BaseLayer.Mem()
	//@ defer fold i.BaseLayer.Mem()
	//@ unfold slices.AbsSlice_Bytes(data, 0, len(data))
	//@ assert forall i int :: minLength <= i && i < len(data) ==> &data[minLength:][i] == &data[minLength + i]
	i.BaseLayer = BaseLayer{
		Contents: data[:minLength],
		Payload:  data[minLength:],
	}
	//@ assert forall l int :: 0 <= l && l < len(i.Payload) ==> &data[minLength+l] == &i.Payload[l]
	//@ fold slices.AbsSlice_Bytes(i.Contents, 0, len(i.Contents))
	//@ fold slices.AbsSlice_Bytes(i.Payload, 0, len(i.Payload))
	return nil
}

// SerializeTo writes the serialized form of this layer into the
// SerializationBuffer, implementing gopacket.SerializableLayer.
//@ requires b != nil
//@ requires i.Mem()
//@ requires b.Mem(buf_init)
//@ ensures err == nil ==> buf_res != nil
//@ ensures err == nil ==> i.Mem() && b.Mem(buf_res)
//@ ensures err != nil ==> b.Mem(buf_init)
//@ ensures err != nil ==> err.ErrorMem()
//@ decreases
func (i *SCMPDestinationUnreachable) SerializeTo(b gopacket.SerializeBuffer, opts gopacket.SerializeOptions/*@, ghost buf_init []byte @*/) (err error/*@, ghost buf_res []byte @*/) {

	buf, err/*@, buf_res@*/ := b.PrependBytes(4/*@, buf_init@*/)
	if err != nil {
		return err/*@, buf_res@*/
	}
	//@ assert buf === buf_res[:4]
	//@ b.ExchangePred(buf_res)
	//@ slices.SplitByIndex_Bytes(buf_res, 0, len(buf_res), 4, writePerm)
	//@ unfold slices.AbsSlice_Bytes(buf_res, 0, 4)
	copy(buf, make([]byte, 4), writePerm)
	//@ fold slices.AbsSlice_Bytes(buf_res, 0, 4)
	//@ slices.CombineAtIndex_Bytes(buf_res, 0, len(buf_res), 4, writePerm)
	//@ apply slices.AbsSlice_Bytes(buf_res, 0, len(buf_res)) --* b.Mem(buf_res)
	return nil/*@, buf_res@*/
}

//@ requires acc(gopacket.LayerTypesMem(), _)
//@ requires acc(&gopacket.LayerTypePayload, _)
//@ requires pb != nil
//@ requires pb.Mem()
//@ requires slices.AbsSlice_Bytes(data, 0, len(data))
//@ ensures err != nil ==> err.ErrorMem()
//@ decreases
func decodeSCMPDestinationUnreachable(data []byte, pb gopacket.PacketBuilder) (err error) {
	s := &SCMPDestinationUnreachable{}
	//@ fold slices.AbsSlice_Bytes(s.Contents, 0, len(s.Contents))
	//@ fold slices.AbsSlice_Bytes(s.Payload, 0, len(s.Payload))
	//@ fold s.BaseLayer.Mem()
	//@ fold s.Mem()
	if err := s.DecodeFromBytes(data, pb); err != nil {
		return err
	}
	pb.AddLayer(s)
	// (VerifiedSCION): The following line needs a small refactor with a temporary variable
	//return pb.NextDecoder(s.NextLayerType())
	next := s.NextLayerType()
	//@ fold next.Mem()
	return pb.NextDecoder(next)
}

// SCMPPacketTooBig represents the structure of a packet too big message.
//
//  +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//  |            reserved           |             MTU               |
//  +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//
type SCMPPacketTooBig struct {
	BaseLayer
	
	MTU uint16
}

// LayerType returns LayerTypeSCMPParameterProblem.
//@ decreases
//@ pure
func (i *SCMPPacketTooBig) LayerType() gopacket.LayerType {
	// (VerifiedSCION) TODO: replace with global
	return getLayerTypeSCMPPacketTooBig()
}

// NextLayerType returns the layer type contained by this DecodingLayer.
//@ preserves acc(&gopacket.LayerTypePayload, _)
//@ decreases
func (*SCMPPacketTooBig) NextLayerType() gopacket.LayerType {
	return gopacket.LayerTypePayload
}

// DecodeFromBytes decodes the given bytes into this layer.
//@ requires df != nil
//@ requires df.Mem()
//@ requires slices.AbsSlice_Bytes(data, 0, len(data))
//@ requires i.Mem()
//@ ensures i.Mem()
//@ ensures df.Mem()
//@ ensures res != nil ==> slices.AbsSlice_Bytes(data, 0, len(data))
//@ ensures res != nil ==> res.ErrorMem()
//@ decreases
func (i *SCMPPacketTooBig) DecodeFromBytes(data []byte, df gopacket.DecodeFeedback) (res error) {
	minLength := 2 + 2
	if size := len(data); size < minLength {
		df.SetTruncated()
		return serrors.New("buffer too short", "min", minLength, "actual", size)
	}
	//@ unfold i.Mem()
	//@ defer fold i.Mem()
	//@ requires acc(&i.MTU)
	//@ requires len(data) >= 4
	//@ preserves slices.AbsSlice_Bytes(data, 0, len(data))
	//@ ensures acc(&i.MTU)
	//@ decreases
	//@ outline (
	//@ slices.SplitByIndex_Bytes(data, 0, len(data), 2, writePerm)
	//@ slices.SplitByIndex_Bytes(data, 2, len(data), 4, writePerm)
	//@ unfold slices.AbsSlice_Bytes(data, 2, 4)
	//@ assert forall i int :: 0 <= i && i < 2 ==> &data[2:4][i] == &data[2 + i]
	i.MTU = binary.BigEndian.Uint16(data[2:4])
	//@ fold slices.AbsSlice_Bytes(data, 2, 4)
	//@ slices.CombineAtIndex_Bytes(data, 0, 4, 2, writePerm)
	//@ slices.CombineAtIndex_Bytes(data, 0, len(data), 4, writePerm)
	//@ )
	//@ requires len(data) >= 4
	//@ requires i.BaseLayer.Mem()
	//@ requires slices.AbsSlice_Bytes(data, 0, len(data))
	//@ ensures i.BaseLayer.Mem()
	//@ decreases
	//@ outline (
	//@ unfold slices.AbsSlice_Bytes(data, 0, len(data))
	//@ unfold i.BaseLayer.Mem()
	//@ assert forall i int :: 0 <= i && i < len(data) ==> &data[4:][i] == &data[4 + i]
	i.BaseLayer = BaseLayer{
		Contents: data[:4],
		Payload:  data[4:],
	}
	//@ assert forall l int :: 0 <= l && l < len(i.Payload) ==> &data[4+l] == &i.Payload[l]
	//@ fold slices.AbsSlice_Bytes(i.Contents, 0, len(i.Contents))
	//@ fold slices.AbsSlice_Bytes(i.Payload, 0, len(i.Payload))
	//@ fold i.BaseLayer.Mem()
	//@ )
	return nil
}

// SerializeTo writes the serialized form of this layer into the
// SerializationBuffer, implementing gopacket.SerializableLayer.
//@ requires b != nil
//@ requires i.Mem()
//@ requires b.Mem(buf_init)
//@ ensures err == nil ==> buf_res != nil
//@ ensures err == nil ==> i.Mem() && b.Mem(buf_res)
//@ ensures err != nil ==> b.Mem(buf_init)
//@ ensures err != nil ==> err.ErrorMem()
//@ decreases
func (i *SCMPPacketTooBig) SerializeTo(b gopacket.SerializeBuffer, opts gopacket.SerializeOptions/*@, ghost buf_init []byte @*/) (err error/*@, ghost buf_res []byte @*/) {

	buf, err/*@, buf_res@*/ := b.PrependBytes(2 + 2/*@, buf_init@*/)
	if err != nil {
		return err/*@, buf_res@*/
	}
	//@ unfold i.Mem()
	//@ defer fold i.Mem()
	//@ requires len(buf_res) >= 4
	//@ requires buf === buf_res[:4]
	//@ requires b != nil
	//@ preserves b.Mem(buf_res)
	//@ decreases
	//@ outline (
	//@ b.ExchangePred(buf_res)
	//@ slices.SplitByIndex_Bytes(buf_res, 0, len(buf_res), 2, writePerm)
	//@ unfold slices.AbsSlice_Bytes(buf_res, 0, 2)
	binary.BigEndian.PutUint16(buf[0:2], uint16(0)) //Reserved
	//@ fold slices.AbsSlice_Bytes(buf_res, 0, 2)
	//@ slices.CombineAtIndex_Bytes(buf_res, 0, len(buf_res), 2, writePerm)
	//@ apply slices.AbsSlice_Bytes(buf_res, 0, len(buf_res)) --* b.Mem(buf_res)
	//@ )
	//@ requires len(buf_res) >= 4
	//@ requires buf === buf_res[:4]
	//@ requires b != nil
	//@ requires acc(&i.MTU)
	//@ requires b.Mem(buf_res)
	//@ ensures acc(&i.MTU)
	//@ ensures b.Mem(buf_res)
	//@ decreases
	//@ outline (
	//@ b.ExchangePred(buf_res)
	//@ slices.SplitByIndex_Bytes(buf_res, 0, len(buf_res), 2, writePerm)
	//@ slices.SplitByIndex_Bytes(buf_res, 2, len(buf_res), 4, writePerm)
	//@ unfold slices.AbsSlice_Bytes(buf_res, 2, 4)
	//@ assert forall i int :: 0 <= i && i < 2 ==> &buf[2:4][i] == &buf[2 + i]
	binary.BigEndian.PutUint16(buf[2:4], i.MTU)
	//@ fold slices.AbsSlice_Bytes(buf_res, 2, 4)
	//@ slices.CombineAtIndex_Bytes(buf_res, 2, len(buf_res), 4, writePerm)
	//@ slices.CombineAtIndex_Bytes(buf_res, 0, len(buf_res), 2, writePerm)
	//@ apply slices.AbsSlice_Bytes(buf_res, 0, len(buf_res)) --* b.Mem(buf_res)
	//@ )
	return nil/*@, buf_res@*/
}

//@ requires acc(gopacket.LayerTypesMem(), _)
//@ requires acc(&gopacket.LayerTypePayload, _)
//@ requires pb != nil
//@ requires pb.Mem()
//@ requires slices.AbsSlice_Bytes(data, 0, len(data))
//@ ensures err != nil ==> err.ErrorMem()
//@ decreases
func decodeSCMPPacketTooBig(data []byte, pb gopacket.PacketBuilder) (err error) {
	s := &SCMPPacketTooBig{}
	//@ fold slices.AbsSlice_Bytes(s.Contents, 0, len(s.Contents))
	//@ fold slices.AbsSlice_Bytes(s.Payload, 0, len(s.Payload))
	//@ fold s.BaseLayer.Mem()
	//@ fold s.Mem()
	if err := s.DecodeFromBytes(data, pb); err != nil {
		return err
	}
	pb.AddLayer(s)
	// (VerifiedSCION): The following line needs a small refactor with a temporary variable
	//return pb.NextDecoder(s.NextLayerType())
	next := s.NextLayerType()
	//@ fold next.Mem()
	return pb.NextDecoder(next)
}
