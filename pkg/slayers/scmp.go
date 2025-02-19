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
	// @ . "github.com/scionproto/scion/verification/utils/definitions"
	// @ sl "github.com/scionproto/scion/verification/utils/slices"
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
// @ pure
// @ decreases
func (s *SCMP) LayerType() gopacket.LayerType {
	return LayerTypeSCMP
}

// CanDecode returns the set of layer types that this DecodingLayer can decode.
// @ ensures res != nil && res === LayerClassSCMP
// @ ensures typeOf(res) == gopacket.LayerType
// @ decreases
func (s *SCMP) CanDecode() (res gopacket.LayerClass) {
	// @ LayerClassSCMPIsLayerType()
	return LayerClassSCMP
}

// NextLayerType use the typecode to select the right next decoder.
// If the SCMP type is unknown, the next layer is gopacket.LayerTypePayload.
// NextLayerType returns the layer type contained by this DecodingLayer.
// @ preserves acc(s.Mem(ub), R20)
// @ decreases
func (s *SCMP) NextLayerType( /*@ ghost ub []byte @*/ ) gopacket.LayerType {
	switch /*@unfolding acc(s.Mem(ub), R20) in @*/ s.TypeCode.Type() {
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
// @ requires  b != nil
// @ requires  s.Mem(ubufMem)
// @ preserves b.Mem()
// @ preserves 0 <= 0 && 0 <= len(b.UBuf()) && len(b.UBuf()) <= cap(b.UBuf()) && forall i int :: { &b.UBuf()[i] } 0 <= i && i < len(b.UBuf()) ==> acc(&b.UBuf()[i])
// @ ensures   err == nil ==> s.Mem(ubufMem)
// @ ensures   err != nil ==> err.ErrorMem()
// @ decreases
func (s *SCMP) SerializeTo(b gopacket.SerializeBuffer, opts gopacket.SerializeOptions /*@, ghost ubufMem []byte @*/) (err error) {
	bytes, err := b.PrependBytes(4)
	// @ underlyingBufRes := b.UBuf()
	if err != nil {
		return err
	}
	// @ unfold s.Mem(ubufMem)

	// @ assert forall i int :: { &bytes[i] } 0 <= i && i < 2 ==> &bytes[i] == &underlyingBufRes[i]

	s.TypeCode.SerializeTo(bytes)



	if opts.ComputeChecksums {
		if s.scn == nil {
			// @ fold s.Mem(ubufMem)
			return serrors.New("can not calculate checksum without SCION header")
		}
		// zero out checksum bytes

		// @ assert forall i int :: { &bytes[i] } 0 <= i && i < 4 ==> &bytes[i] == &underlyingBufRes[i]
		bytes[2] = 0
		bytes[3] = 0

		verScionTmp := b.Bytes()
		// @ unfold s.scn.ChecksumMem()
		s.Checksum, err = s.scn.computeChecksum(verScionTmp, uint8(L4SCMP))
		// @ fold s.scn.ChecksumMem()
		if err != nil {
			// @ fold s.Mem(ubufMem)
			return err
		}

	}

	// @ assert forall i int :: { &bytes[i] } 0 <= i && i < 4 ==> &bytes[i] == &underlyingBufRes[i]
	// @ assert forall i int :: { &bytes[2:][i] } 0 <= i && i < 2 ==> &bytes[2:][i] == &bytes[i + 2]
	binary.BigEndian.PutUint16(bytes[2:], s.Checksum)

	// @ fold s.Mem(ubufMem)
	return nil
}

// DecodeFromBytes decodes the given bytes into this layer.
// @ requires  df != nil
// @ preserves 0 <= 0 && 0 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < len(data) ==> acc(&data[i], R40)
// @ requires  s.NonInitMem()
// @ preserves df.Mem()
// @ ensures   res == nil ==> s.Mem(data)
// @ ensures   res != nil ==> (s.NonInitMem() && res.ErrorMem())
// @ decreases
func (s *SCMP) DecodeFromBytes(data []byte, df gopacket.DecodeFeedback) (res error) {
	if size := len(data); size < 4 {
		df.SetTruncated()
		return serrors.New("SCMP layer length is less then 4 bytes", "minimum", 4, "actual", size)
	}
	// @ unfold s.NonInitMem()
	// @ requires len(data) >= 4
	// @ requires 0 <= 0 && 0 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < len(data) ==> acc(&data[i], R40)
	// @ preserves acc(&s.TypeCode)
	// @ ensures 0 <= 2 && 2 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 2 <= i && i < len(data) ==> acc(&data[i], R40)
	// @ ensures 0 <= 0 && 0 <= 2 && 2 <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < 2 ==> acc(&data[i], R40)
	// @ decreases
	// @ outline (

	s.TypeCode = CreateSCMPTypeCode(SCMPType(data[0]), SCMPCode(data[1]))

	// @ )
	// @ requires len(data) >= 4
	// @ requires 0 <= 0 && 0 <= 2 && 2 <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < 2 ==> acc(&data[i], R40)
	// @ requires 0 <= 2 && 2 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 2 <= i && i < len(data) ==> acc(&data[i], R40)
	// @ preserves acc(&s.Checksum)
	// @ ensures 0 <= 0 && 0 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < len(data) ==> acc(&data[i], R40)
	// @ decreases
	// @ outline (

	// @ assert forall i int :: { &data[2:4][i] } 0 <= i && i < 2 ==> &data[2 + i] == &data[2:4][i]
	s.Checksum = binary.BigEndian.Uint16(data[2:4])

	// @ )
	s.BaseLayer = BaseLayer{Contents: data[:4], Payload: data[4:]}
	// @ fold s.BaseLayer.Mem(data, 4)
	// @ fold s.Mem(data)
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
// @ preserves acc(&s.scn)
// @ ensures   s.scn == scn
// @ decreases
func (s *SCMP) SetNetworkLayerForChecksum(scn *SCION) {
	s.scn = scn
}

// @ requires  pb != nil
// @ requires  0 <= 0 && 0 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < len(data) ==> acc(&data[i])
// @ preserves pb.Mem()
// @ ensures   res != nil ==> res.ErrorMem()
// @ decreases
func decodeSCMP(data []byte, pb gopacket.PacketBuilder) (res error) {
	scmp := &SCMP{}
	// @ fold scmp.NonInitMem()
	err := scmp.DecodeFromBytes(data, pb)
	if err != nil {
		return err
	}
	pb.AddLayer(scmp)
	verScionTmp := scmp.NextLayerType( /*@ data @*/ )
	// @ fold verScionTmp.Mem()
	return pb.NextDecoder(verScionTmp)
}
