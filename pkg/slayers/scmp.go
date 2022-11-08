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
	"fmt"

	"github.com/google/gopacket"

	"github.com/scionproto/scion/pkg/private/serrors"
	// @ def "github.com/scionproto/scion/verification/utils/definitions"
	// @ "github.com/scionproto/scion/verification/utils/slices"
)

// MaxSCMPPacketLen the maximum length a SCION packet including SCMP quote can
// have. This length includes the SCION, and SCMP header of the packet.
//
//	+-------------------------+
//	|        Underlay         |
//	+-------------------------+
//	|          SCION          |  \
//	|          SCMP           |   \
//	+-------------------------+    \_ MaxSCMPPacketLen
//	|          Quote:         |    /
//	|        SCION Orig       |   /
//	|         L4 Orig         |  /
//	+-------------------------+
const MaxSCMPPacketLen = 1232

// SCMP is the SCMP header on top of SCION header.
//
//	 0                   1                   2                   3
//	 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
//	+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//	|     Type      |     Code      |           Checksum            |
//	+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//	|                            InfoBlock                          |
//	+                                                               +
//	|                         (variable length)                     |
//	+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//	|                            DataBlock                          |
//	+                                                               +
//	|                         (variable length)                     |
//	+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
type SCMP struct {
	BaseLayer
	TypeCode SCMPTypeCode
	Checksum uint16

	scn *SCION
}

// LayerType returns LayerTypeSCMP.
// @ decreases
// @ pure
func (s *SCMP) LayerType() gopacket.LayerType {
	return LayerTypeSCMP
}

// CanDecode returns the set of layer types that this DecodingLayer can decode.
// @ decreases
// @ pure
func (s *SCMP) CanDecode() gopacket.LayerClass {
	return LayerClassSCMP
}

// NextLayerType use the typecode to select the right next decoder.
// If the SCMP type is unknown, the next layer is gopacket.LayerTypePayload.
// NextLayerType returns the layer type contained by this DecodingLayer.
// @ preserves acc(s.Mem(), def.ReadL20)
// @ decreases
func (s *SCMP) NextLayerType() gopacket.LayerType {
	switch /*@unfolding acc(s.Mem(), def.ReadL20) in @*/s.TypeCode.Type() {
	case SCMPTypeDestinationUnreachable:
		return LayerTypeSCMPDestinationUnreachable
	case SCMPTypePacketTooBig:
		return LayerTypeSCMPPacketTooBig
	case SCMPTypeParameterProblem:
		return LayerTypeSCMPParameterProblem
	case SCMPTypeExternalInterfaceDown:
		return LayerTypeSCMPExternalInterfaceDown
	case SCMPTypeInternalConnectivityDown:
		return LayerTypeSCMPInternalConnectivityDown
	case SCMPTypeEchoRequest, SCMPTypeEchoReply:
		return LayerTypeSCMPEcho
	case SCMPTypeTracerouteRequest, SCMPTypeTracerouteReply:
		return LayerTypeSCMPTraceroute
	}
	return gopacket.LayerTypePayload
}

// SerializeTo writes the serialized form of this layer into the
// SerializationBuffer, implementing gopacket.SerializableLayer.
// @ requires b != nil
// @ requires s.Mem()
// @ requires b.Mem(underlyingBuf)
// @ ensures err == nil ==> underlyingBufRes != nil
// @ ensures err == nil ==> s.Mem() && b.Mem(underlyingBufRes)
// @ ensures err != nil ==> err.ErrorMem()
// @ decreases
func (s *SCMP) SerializeTo(b gopacket.SerializeBuffer, opts gopacket.SerializeOptions/*@, ghost underlyingBuf []byte @*/) (err error/*@, ghost underlyingBufRes []byte @*/) {
	bytes, err/*@, underlyingBufRes@*/  := b.PrependBytes(4/*@, underlyingBuf@*/)
	if err != nil {
		return err/*@, underlyingBufRes @*/
	}
	// @ unfold s.Mem()
	
	// @ requires len(underlyingBufRes) >= 4
	// @ requires bytes === underlyingBufRes[:4]
	// @ requires b != nil
	// @ preserves acc(&s.TypeCode)
	// @ preserves b.Mem(underlyingBufRes)
	// @ ensures underlyingBufRes === before(underlyingBufRes)
	// @ decreases
	// @ outline (
	// @ b.ExchangePred(underlyingBufRes)
	// @ slices.SplitByIndex_Bytes(underlyingBufRes, 0, len(underlyingBufRes), 2, writePerm)
	// @ unfold slices.AbsSlice_Bytes(underlyingBufRes, 0, 2)
	// @ assert forall i int :: { &bytes[i] } 0 <= i && i < 2 ==> &bytes[i] == &underlyingBufRes[i]
	// @ fold slices.AbsSlice_Bytes(bytes, 0, 2)
	s.TypeCode.SerializeTo(bytes)
	// @ unfold slices.AbsSlice_Bytes(bytes, 0, 2)
	// @ fold slices.AbsSlice_Bytes(underlyingBufRes, 0, 2)
	// @ slices.CombineAtIndex_Bytes(underlyingBufRes, 0, len(underlyingBufRes), 2, writePerm)
	// @ apply slices.AbsSlice_Bytes(underlyingBufRes, 0, len(underlyingBufRes)) --* b.Mem(underlyingBufRes)
	// @ )

	if opts.ComputeChecksums {
		if s.scn == nil {
			// @ fold s.Mem()
			return serrors.New("can not calculate checksum without SCION header")/*@, underlyingBufRes @*/
		}
		// zero out checksum bytes
		// @ requires len(underlyingBufRes) >= 4
		// @ requires bytes === underlyingBufRes[:4]
		// @ requires b != nil
		// @ preserves b.Mem(underlyingBufRes)
		// @ ensures underlyingBufRes === before(underlyingBufRes)
		// @ decreases
		// @ outline (
		// @ b.ExchangePred(underlyingBufRes)
		// @ slices.SplitByIndex_Bytes(underlyingBufRes, 0, len(underlyingBufRes), 4, writePerm)
		// @ unfold slices.AbsSlice_Bytes(underlyingBufRes, 0, 4)
		// @ assert forall i int :: { &bytes[i] } 0 <= i && i < 4 ==> &bytes[i] == &underlyingBufRes[i]
		bytes[2] = 0
		bytes[3] = 0
		// @ fold slices.AbsSlice_Bytes(underlyingBufRes, 0, 4)
		// @ slices.CombineAtIndex_Bytes(underlyingBufRes, 0, len(underlyingBufRes), 4, writePerm)
		// @ apply slices.AbsSlice_Bytes(underlyingBufRes, 0, len(underlyingBufRes)) --* b.Mem(underlyingBufRes)
		// @ )
		verScionTmp := b.Bytes(/*@underlyingBufRes@*/)
		// @ unfold s.scn.ChecksumMem()
		s.Checksum, err = s.scn.computeChecksum(verScionTmp, uint8(L4SCMP))
		// @ fold s.scn.ChecksumMem()
		// @ apply slices.AbsSlice_Bytes(verScionTmp, 0, len(verScionTmp)) --* b.Mem(underlyingBufRes)
		if err != nil {
			// @ fold s.Mem()
			return err/*@, underlyingBufRes @*/
		}

	}
	// @ requires len(underlyingBufRes) >= 4
	// @ requires bytes === underlyingBufRes[:4]
	// @ requires b != nil
	// @ preserves acc(&s.Checksum)
	// @ preserves b.Mem(underlyingBufRes)
	// @ decreases
	// @ outline (
	// @ b.ExchangePred(underlyingBufRes)
	// @ slices.SplitByIndex_Bytes(underlyingBufRes, 0, len(underlyingBufRes), 4, writePerm)
	// @ unfold slices.AbsSlice_Bytes(underlyingBufRes, 0, 4)
	// @ assert forall i int :: { &bytes[i] } 0 <= i && i < 4 ==> &bytes[i] == &underlyingBufRes[i]
	// @ assert forall i int :: { &bytes[2:][i] } 0 <= i && i < 2 ==> &bytes[2:][i] == &bytes[i + 2]
	binary.BigEndian.PutUint16(bytes[2:], s.Checksum)
	// @ fold slices.AbsSlice_Bytes(underlyingBufRes, 0, 4)
	// @ slices.CombineAtIndex_Bytes(underlyingBufRes, 0, len(underlyingBufRes), 4, writePerm)
	// @ apply slices.AbsSlice_Bytes(underlyingBufRes, 0, len(underlyingBufRes)) --* b.Mem(underlyingBufRes)
	// @ )
	// @ fold s.Mem()
	return nil/*@, underlyingBufRes @*/
}

// DecodeFromBytes decodes the given bytes into this layer.
// @ requires df != nil
// @ requires slices.AbsSlice_Bytes(data, 0, len(data))
// @ preserves df.Mem()
// @ preserves s.Mem()
// @ ensures res != nil ==> slices.AbsSlice_Bytes(data, 0, len(data))
// @ ensures res != nil ==> res.ErrorMem()
// @ decreases
func (s *SCMP) DecodeFromBytes(data []byte, df gopacket.DecodeFeedback) (res error) {
	if size := len(data); size < 4 {
		df.SetTruncated()
		return serrors.New("SCMP layer length is less then 4 bytes", "minimum", 4, "actual", size)
	}
	// @ unfold s.Mem()
	// @ defer fold s.Mem()
	// @ requires len(data) >= 4
	// @ requires slices.AbsSlice_Bytes(data, 0, len(data))
	// @ preserves acc(&s.TypeCode)
	// @ ensures slices.AbsSlice_Bytes(data, 2, len(data))
	// @ ensures slices.AbsSlice_Bytes(data, 0, 2)
	// @ decreases
	// @ outline (
	// @ slices.SplitByIndex_Bytes(data, 0, len(data), 2, writePerm)
	// @ unfold slices.AbsSlice_Bytes(data, 0, 2)
	s.TypeCode = CreateSCMPTypeCode(SCMPType(data[0]), SCMPCode(data[1]))
	// @ fold slices.AbsSlice_Bytes(data, 0, 2)
	// @ )
	// @ requires len(data) >= 4
	// @ requires slices.AbsSlice_Bytes(data, 0, 2)
	// @ requires slices.AbsSlice_Bytes(data, 2, len(data))
	// @ preserves acc(&s.Checksum)
	// @ ensures slices.AbsSlice_Bytes(data, 0, len(data))
	// @ decreases
	// @ outline (
	// @ slices.SplitByIndex_Bytes(data, 2, len(data), 4, writePerm)
	// @ unfold slices.AbsSlice_Bytes(data, 2, 4)
	// @ assert forall i int :: { &data[2:4][i] } 0 <= i && i < 2 ==> &data[2 + i] == &data[2:4][i]
	s.Checksum = binary.BigEndian.Uint16(data[2:4])
	// @ fold slices.AbsSlice_Bytes(data, 2, 4)
	// @ slices.CombineAtIndex_Bytes(data, 0, 4, 2, writePerm)
	// @ slices.CombineAtIndex_Bytes(data, 0, len(data), 4, writePerm)
	// @ )
	// @ requires len(data) >= 4
	// @ requires slices.AbsSlice_Bytes(data, 0, len(data))
	// @ preserves s.BaseLayer.Mem()
	// @ decreases
	// @ outline (
	// @ unfold slices.AbsSlice_Bytes(data, 0, len(data))
	// @ unfold s.BaseLayer.Mem()
	// @ assert forall i int :: { &data[4:][i] } 0 <= i && i < len(data) ==> &data[4:][i] == &data[4 + i]
	s.BaseLayer = BaseLayer{Contents: data[:4], Payload: data[4:]}
	// @ assert forall l int :: { &s.Payload[l] } 0 <= l && l < len(s.Payload) ==> &data[4+l] == &s.Payload[l]
	// @ fold slices.AbsSlice_Bytes(s.Contents, 0, len(s.Contents))
	// @ fold slices.AbsSlice_Bytes(s.Payload, 0, len(s.Payload))
	// @ fold s.BaseLayer.Mem()
	// @ )
	return nil
}

// @ requires s != nil
// @ preserves acc(&s.TypeCode) && acc(&s.Checksum) && acc(&s.Payload) && acc(s.Payload)
// @ decreases
func (s *SCMP) String() string {
	return fmt.Sprintf("%s(%d)\nPayload: %s", &s.TypeCode, s.Checksum, s.Payload)
}

// SetNetworkLayerForChecksum tells this layer which network layer is wrapping it.
// This is needed for computing the checksum when serializing,
// TODO: verify this when SCION is a layer
// @ trusted
// @ requires false
func (s *SCMP) SetNetworkLayerForChecksum(l gopacket.NetworkLayer) (err error) {
	if l == nil {
		return serrors.New("cannot use nil layer type for scmp checksum network layer")
	}
	if l.LayerType() != LayerTypeSCION {
		return serrors.New("cannot use layer type for scmp checksum network layer",
			"type", l.LayerType())
	}
	s.scn = l.(*SCION)
	return nil
}

// @ requires pb != nil
// @ preserves pb.Mem()
// @ requires slices.AbsSlice_Bytes(data, 0, len(data))
// @ ensures err != nil ==> err.ErrorMem()
// @ decreases
func decodeSCMP(data []byte, pb gopacket.PacketBuilder) (err error) {
	scmp := &SCMP{}
	// @ fold slices.AbsSlice_Bytes(scmp.Contents, 0, len(scmp.Contents))
	// @ fold slices.AbsSlice_Bytes(scmp.Payload, 0, len(scmp.Payload))
	// @ fold scmp.BaseLayer.Mem()
	// @ assert scmp.scn == nil
	// @ fold scmp.Mem()
	err := scmp.DecodeFromBytes(data, pb)
	if err != nil {
		return err
	}
	pb.AddLayer(scmp)
	verScionTmp := scmp.NextLayerType()
	// @ fold verScionTmp.Mem()
	return pb.NextDecoder(verScionTmp)
}
