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

// TODO: remove this when scion.go is merged in
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

//@ pred (b *BaseLayer) Mem() {
//@ 	acc(b) && acc(b.Contents) && acc(b.Payload)
//@ }

//@ pred (b *BaseLayer) LayerMem() {
//@ 	acc(b) && acc(b.Contents)
//@ }

//@ pred (b *BaseLayer) PayloadMem() {
//@ 	acc(b) && acc(b.Payload)
//@ }

//@ requires b.LayerMem()
//@ ensures slices.AbsSlice_Bytes(res, 0, len(res))
//@ ensures slices.AbsSlice_Bytes(res, 0, len(res)) --* b.LayerMem()
//@ decreases
func (b *BaseLayer) LayerContents() (res []byte) {
	//@ unfold b.LayerMem()
	res = b.Contents
	//@ fold slices.AbsSlice_Bytes(res, 0, len(res))
	//@ package slices.AbsSlice_Bytes(res, 0, len(res)) --* b.LayerMem() {
	//@ 	unfold slices.AbsSlice_Bytes(res, 0, len(res))
	//@ 	fold b.LayerMem()
	//@ }
}

//@ requires b.PayloadMem()
//@ ensures slices.AbsSlice_Bytes(res, 0, len(res))
//@ ensures slices.AbsSlice_Bytes(res, 0, len(res)) --* b.PayloadMem()
//@ decreases
func (b *BaseLayer) LayerPayload() (res []byte) {
	//@ unfold b.PayloadMem()
	res = b.Payload
	//@ fold slices.AbsSlice_Bytes(res, 0, len(res))
	//@ package slices.AbsSlice_Bytes(res, 0, len(res)) --* b.PayloadMem() {
	//@ 	unfold slices.AbsSlice_Bytes(res, 0, len(res))
	//@ 	fold b.PayloadMem()
	//@ }
}

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

// LayerType returns LayerTypeSCMPExternalInterfaceDown.
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
//@ ensures res != nil ==> res.ErrorMem()
//@ decreases
func (i *SCMPExternalInterfaceDown) DecodeFromBytes(data []byte,
	df gopacket.DecodeFeedback) (res error) {

	minLength := addr.IABytes + scmpRawInterfaceLen
	if size := len(data); size < minLength {
		df.SetTruncated()
		return serrors.New("buffer too short", "mininum_legth", minLength, "actual", size)
	}
	assert len(data) == 16
	//@ unfold i.Mem()
	//@ defer fold i.Mem()
	offset := 0
	//@ preserves slices.AbsSlice_Bytes(data, 0, len(data))
	//@ decreases
	//@ outline (
	//@ assert len(data) > 8
	//@ unfold slices.AbsSlice_Bytes(data, 0, len(data))
	//@ assert acc(&data[0], _) && acc(&data[1], _) && acc(&data[2], _) && acc(&data[3], _) && acc(&data[4], _) && acc(&data[5], _) && acc(&data[6], _) && acc(&data[7], _)
	i.IA = addr.IA(binary.BigEndian.Uint64(data[offset:]))
	//@ fold slices.AbsSlice_Bytes(data, 0, len(data))
	//@ )
	offset += addr.IABytes
	i.IfID = binary.BigEndian.Uint64(data[offset : offset+scmpRawInterfaceLen])
	offset += scmpRawInterfaceLen
	i.BaseLayer = BaseLayer{
		Contents: data[:offset],
		Payload:  data[offset:],
	}
	return nil
}

// SerializeTo writes the serialized form of this layer into the
// SerializationBuffer, implementing gopacket.SerializableLayer.
//@ trusted
//@ requires i != nil
//@ requires b != nil
//@ requires b.Mem(buf_init)
//@ preserves i.Mem()
//@ ensures err == nil ==> buf_res != nil
//@ ensures err == nil ==> b.Mem(buf_res)
//@ ensures err != nil ==> b.Mem(buf_init)
//@ ensures err != nil ==> err.ErrorMem()
//@ decreases
func (i *SCMPExternalInterfaceDown) SerializeTo(b gopacket.SerializeBuffer, opts gopacket.SerializeOptions/*@, ghost buf_init []byte @*/) (err error/*@, ghost buf_res []byte @*/) {

	buf, err/*@, buf_res@*/ := b.PrependBytes(addr.IABytes + scmpRawInterfaceLen/*@, buf_init@*/)
	//assert false
	if err != nil {
		return err/*@, buf_res @*/
	}
	//assert false
	offset := 0
	//@ unfold i.Mem()
	//@ defer fold i.Mem()
	binary.BigEndian.PutUint64(buf[offset:], uint64(i.IA))
	offset += addr.IABytes
	binary.BigEndian.PutUint64(buf[offset:offset+scmpRawInterfaceLen], i.IfID)
	return nil, buf_res
}

//@ trusted
//@ preserves slices.AbsSlice_Bytes(data, 0, len(data))
//@ ensures err != nil ==> err.ErrorMem()
//@ decreases
func decodeSCMPExternalInterfaceDown(data []byte, pb gopacket.PacketBuilder) (err error) {
	s := &SCMPExternalInterfaceDown{}
	err := s.DecodeFromBytes(data, pb)
	if err != nil {
		return err
	}
	pb.AddLayer(s)
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
//@ trusted
//@ decreases _
func (*SCMPInternalConnectivityDown) LayerType() gopacket.LayerType {
	return LayerTypeSCMPInternalConnectivityDown
}

// NextLayerType returns the layer type contained by this DecodingLayer.
//@ trusted
//@ decreases _
func (*SCMPInternalConnectivityDown) NextLayerType() gopacket.LayerType {
	return gopacket.LayerTypePayload
}

// DecodeFromBytes decodes the given bytes into this layer.
//@ trusted
//@ decreases _
func (i *SCMPInternalConnectivityDown) DecodeFromBytes(data []byte,
	df gopacket.DecodeFeedback) error {

	minLength := addr.IABytes + 2*scmpRawInterfaceLen
	if size := len(data); size < minLength {
		df.SetTruncated()
		return serrors.New("buffer too short", "mininum_legth", minLength, "actual", size)
	}
	offset := 0
	i.IA = addr.IA(binary.BigEndian.Uint64(data[offset:]))
	offset += addr.IABytes
	i.Ingress = binary.BigEndian.Uint64(data[offset : offset+scmpRawInterfaceLen])
	offset += scmpRawInterfaceLen
	i.Egress = binary.BigEndian.Uint64(data[offset : offset+scmpRawInterfaceLen])
	offset += scmpRawInterfaceLen
	i.BaseLayer = BaseLayer{
		Contents: data[:offset],
		Payload:  data[offset:],
	}
	return nil
}

// SerializeTo writes the serialized form of this layer into the
// SerializationBuffer, implementing gopacket.SerializableLayer.
//@ trusted
//@ decreases _
func (i *SCMPInternalConnectivityDown) SerializeTo(b gopacket.SerializeBuffer,
	opts gopacket.SerializeOptions) error {

	buf, err := b.PrependBytes(addr.IABytes + 2*scmpRawInterfaceLen)
	if err != nil {
		return err
	}
	offset := 0
	binary.BigEndian.PutUint64(buf[offset:], uint64(i.IA))
	offset += addr.IABytes
	binary.BigEndian.PutUint64(buf[offset:offset+scmpRawInterfaceLen], i.Ingress)
	offset += scmpRawInterfaceLen
	binary.BigEndian.PutUint64(buf[offset:offset+scmpRawInterfaceLen], i.Egress)
	return nil
}

//@ trusted
//@ decreases _
func decodeSCMPInternalConnectivityDown(data []byte, pb gopacket.PacketBuilder) error {
	s := &SCMPInternalConnectivityDown{}
	if err := s.DecodeFromBytes(data, pb); err != nil {
		return err
	}
	pb.AddLayer(s)
	return pb.NextDecoder(s.NextLayerType())
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
//@ trusted
//@ decreases _
func (*SCMPEcho) LayerType() gopacket.LayerType {
	return LayerTypeSCMPEcho
}

// NextLayerType returns the layer type contained by this DecodingLayer.
//@ trusted
//@ decreases _
func (*SCMPEcho) NextLayerType() gopacket.LayerType {
	return gopacket.LayerTypePayload
}

// DecodeFromBytes decodes the given bytes into this layer.
//@ trusted
//@ decreases _
func (i *SCMPEcho) DecodeFromBytes(data []byte, df gopacket.DecodeFeedback) error {
	minLength := 4
	if size := len(data); size < minLength {
		df.SetTruncated()
		return serrors.New("buffer too short", "min", minLength, "actual", size)
	}
	offset := 0
	i.Identifier = binary.BigEndian.Uint16(data[:2])
	offset += 2
	i.SeqNumber = binary.BigEndian.Uint16(data[offset : offset+2])
	offset += 2
	i.BaseLayer = BaseLayer{
		Contents: data[:offset],
		Payload:  data[offset:],
	}
	return nil
}

// SerializeTo writes the serialized form of this layer into the
// SerializationBuffer, implementing gopacket.SerializableLayer.
//@ trusted
//@ decreases _
func (i *SCMPEcho) SerializeTo(b gopacket.SerializeBuffer, opts gopacket.SerializeOptions) error {
	buf, err := b.PrependBytes(4)
	if err != nil {
		return err
	}
	offset := 0
	binary.BigEndian.PutUint16(buf[:2], i.Identifier)
	offset += 2
	binary.BigEndian.PutUint16(buf[offset:offset+2], i.SeqNumber)
	return nil
}

//@ trusted
//@ decreases _
func decodeSCMPEcho(data []byte, pb gopacket.PacketBuilder) error {
	s := &SCMPEcho{}
	if err := s.DecodeFromBytes(data, pb); err != nil {
		return err
	}
	pb.AddLayer(s)
	return pb.NextDecoder(s.NextLayerType())
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
//@ trusted
//@ decreases _
func (*SCMPParameterProblem) LayerType() gopacket.LayerType {
	return LayerTypeSCMPParameterProblem
}

// NextLayerType returns the layer type contained by this DecodingLayer.
//@ trusted
//@ decreases _
func (*SCMPParameterProblem) NextLayerType() gopacket.LayerType {
	return gopacket.LayerTypePayload
}

// DecodeFromBytes decodes the given bytes into this layer.
//@ trusted
//@ decreases _
func (i *SCMPParameterProblem) DecodeFromBytes(data []byte, df gopacket.DecodeFeedback) error {
	minLength := 2 + 2
	if size := len(data); size < minLength {
		df.SetTruncated()
		return serrors.New("buffer too short", "min", minLength, "actual", size)
	}
	i.Pointer = binary.BigEndian.Uint16(data[2:4])
	i.BaseLayer = BaseLayer{
		Contents: data[:4],
		Payload:  data[4:],
	}
	return nil
}

// SerializeTo writes the serialized form of this layer into the
// SerializationBuffer, implementing gopacket.SerializableLayer.
//@ trusted
//@ decreases _
func (i *SCMPParameterProblem) SerializeTo(b gopacket.SerializeBuffer,
	opts gopacket.SerializeOptions) error {

	buf, err := b.PrependBytes(2 + 2)
	if err != nil {
		return err
	}
	binary.BigEndian.PutUint16(buf[0:2], uint16(0)) //Reserved
	binary.BigEndian.PutUint16(buf[2:4], i.Pointer)
	return nil
}

//@ trusted
//@ decreases _
func decodeSCMPParameterProblem(data []byte, pb gopacket.PacketBuilder) error {
	s := &SCMPParameterProblem{}
	if err := s.DecodeFromBytes(data, pb); err != nil {
		return err
	}
	pb.AddLayer(s)
	return pb.NextDecoder(s.NextLayerType())
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
//@ trusted
//@ decreases _
func (*SCMPTraceroute) LayerType() gopacket.LayerType {
	return LayerTypeSCMPTraceroute
}

// NextLayerType returns the layer type contained by this DecodingLayer.
//@ trusted
//@ decreases _
func (*SCMPTraceroute) NextLayerType() gopacket.LayerType {
	return gopacket.LayerTypePayload
}

// DecodeFromBytes decodes the given bytes into this layer.
//@ trusted
//@ decreases _
func (i *SCMPTraceroute) DecodeFromBytes(data []byte, df gopacket.DecodeFeedback) error {
	minLength := 2 + 2 + addr.IABytes + scmpRawInterfaceLen
	if size := len(data); size < minLength {
		df.SetTruncated()
		return serrors.New("buffer too short", "min", minLength, "actual", size)
	}
	offset := 0
	i.Identifier = binary.BigEndian.Uint16(data[offset : offset+2])
	offset += 2
	i.Sequence = binary.BigEndian.Uint16(data[offset : offset+2])
	offset += 2
	i.IA = addr.IA(binary.BigEndian.Uint64(data[offset : offset+addr.IABytes]))
	offset += addr.IABytes
	i.Interface = binary.BigEndian.Uint64(data[offset : offset+scmpRawInterfaceLen])
	offset += scmpRawInterfaceLen
	i.BaseLayer = BaseLayer{
		Contents: data[:offset],
		Payload:  data[offset:],
	}
	return nil
}

// SerializeTo writes the serialized form of this layer into the
// SerializationBuffer, implementing gopacket.SerializableLayer.
//@ trusted
//@ decreases _
func (i *SCMPTraceroute) SerializeTo(b gopacket.SerializeBuffer,
	opts gopacket.SerializeOptions) error {

	buf, err := b.PrependBytes(2 + 2 + addr.IABytes + scmpRawInterfaceLen)
	if err != nil {
		return err
	}
	offset := 0
	binary.BigEndian.PutUint16(buf[:2], i.Identifier)
	offset += 2
	binary.BigEndian.PutUint16(buf[offset:offset+2], i.Sequence)
	offset += 2
	binary.BigEndian.PutUint64(buf[offset:offset+addr.IABytes], uint64(i.IA))
	offset += addr.IABytes
	binary.BigEndian.PutUint64(buf[offset:offset+scmpRawInterfaceLen], i.Interface)
	return nil
}

//@ trusted
//@ decreases _
func decodeSCMPTraceroute(data []byte, pb gopacket.PacketBuilder) error {
	s := &SCMPTraceroute{}
	if err := s.DecodeFromBytes(data, pb); err != nil {
		return err
	}
	pb.AddLayer(s)
	return pb.NextDecoder(s.NextLayerType())
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
//@ trusted
//@ decreases _
func (*SCMPDestinationUnreachable) LayerType() gopacket.LayerType {
	return LayerTypeSCMPDestinationUnreachable
}

// NextLayerType returns the layer type contained by this DecodingLayer.
//@ trusted
//@ decreases _
func (*SCMPDestinationUnreachable) NextLayerType() gopacket.LayerType {
	return gopacket.LayerTypePayload
}

// DecodeFromBytes decodes the given bytes into this layer.
//@ trusted
//@ decreases _
func (i *SCMPDestinationUnreachable) DecodeFromBytes(data []byte,
	df gopacket.DecodeFeedback) error {

	minLength := 4
	if size := len(data); size < minLength {
		df.SetTruncated()
		return serrors.New("buffer too short", "min", minLength, "actual", size)
	}
	i.BaseLayer = BaseLayer{
		Contents: data[:minLength],
		Payload:  data[minLength:],
	}
	return nil
}

// SerializeTo writes the serialized form of this layer into the
// SerializationBuffer, implementing gopacket.SerializableLayer.
//@ trusted
//@ decreases _
func (i *SCMPDestinationUnreachable) SerializeTo(b gopacket.SerializeBuffer,
	opts gopacket.SerializeOptions) error {

	buf, err := b.PrependBytes(4)
	if err != nil {
		return err
	}
	copy(buf, make([]byte, 4))
	return nil
}

//@ trusted
//@ decreases _
func decodeSCMPDestinationUnreachable(data []byte, pb gopacket.PacketBuilder) error {
	s := &SCMPDestinationUnreachable{}
	if err := s.DecodeFromBytes(data, pb); err != nil {
		return err
	}
	pb.AddLayer(s)
	return pb.NextDecoder(s.NextLayerType())
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
//@ trusted
//@ decreases _
func (*SCMPPacketTooBig) LayerType() gopacket.LayerType {
	return LayerTypeSCMPPacketTooBig
}

// NextLayerType returns the layer type contained by this DecodingLayer.
//@ trusted
//@ decreases _
func (*SCMPPacketTooBig) NextLayerType() gopacket.LayerType {
	return gopacket.LayerTypePayload
}

// DecodeFromBytes decodes the given bytes into this layer.
//@ trusted
//@ decreases _
func (i *SCMPPacketTooBig) DecodeFromBytes(data []byte, df gopacket.DecodeFeedback) error {
	minLength := 2 + 2
	if size := len(data); size < minLength {
		df.SetTruncated()
		return serrors.New("buffer too short", "min", minLength, "actual", size)
	}
	i.MTU = binary.BigEndian.Uint16(data[2:4])
	i.BaseLayer = BaseLayer{
		Contents: data[:4],
		Payload:  data[4:],
	}
	return nil
}

// SerializeTo writes the serialized form of this layer into the
// SerializationBuffer, implementing gopacket.SerializableLayer.
//@ trusted
//@ decreases _
func (i *SCMPPacketTooBig) SerializeTo(b gopacket.SerializeBuffer,
	opts gopacket.SerializeOptions) error {

	buf, err := b.PrependBytes(2 + 2)
	if err != nil {
		return err
	}
	binary.BigEndian.PutUint16(buf[0:2], uint16(0)) //Reserved
	binary.BigEndian.PutUint16(buf[2:4], i.MTU)
	return nil
}

//@ trusted
//@ decreases _
func decodeSCMPPacketTooBig(data []byte, pb gopacket.PacketBuilder) error {
	s := &SCMPPacketTooBig{}
	if err := s.DecodeFromBytes(data, pb); err != nil {
		return err
	}
	pb.AddLayer(s)
	return pb.NextDecoder(s.NextLayerType())
}
