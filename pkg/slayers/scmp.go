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
// @ requires acc(s.Mem(), _)
// @ decreases
// @ pure
func (s *SCMP) LayerType() gopacket.LayerType {
	return /*@ unfolding acc(s.Mem(), _) in @*/ LayerTypeSCMP
}

// CanDecode returns the set of layer types that this DecodingLayer can decode.
// @ requires acc(s.Mem(), _)
// @ decreases
// @ pure
func (s *SCMP) CanDecode() gopacket.LayerClass {
	return /*@ unfolding acc(s.Mem(), _) in @*/ LayerClassSCMP
}

// NextLayerType use the typecode to select the right next decoder.
// If the SCMP type is unknown, the next layer is gopacket.LayerTypePayload.
// NextLayerType returns the layer type contained by this DecodingLayer.
// @ requires acc(&LayerTypeSCMPDestinationUnreachable, _)
// @ requires acc(&LayerTypeSCMPPacketTooBig, _)
// @ requires acc(&LayerTypeSCMPParameterProblem, _)
// @ requires acc(&LayerTypeSCMPExternalInterfaceDown, _)
// @ requires acc(&LayerTypeSCMPInternalConnectivityDown, _)
// @ requires acc(&LayerTypeSCMPEcho, _)
// @ requires acc(&LayerTypeSCMPTraceroute, _)
// @ requires acc(&gopacket.LayerTypePayload, _)
// @ requires acc(s.Mem(), def.ReadL20)
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
// @ ensures err != nil ==> b.Mem(underlyingBuf)
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
	// @ ensures &s.TypeCode == before(&s.TypeCode)
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
			// @ assert acc(&LayerTypeSCMP, _) && acc(&LayerClassSCMP, _) && acc(&s.TypeCode)
			// @ assert acc(&s.Checksum)
			// @ assert s.BaseLayer.Mem()
			// @ assert acc(&s.scn)
			// @ assert (s != nil ==> s.scn.ChecksumMem())
			// @ fold s.Mem()
			return serrors.New("can not calculate checksum without SCION header")/*@, underlyingBufRes @*/
		}
		// zero out checksum bytes
		// @ requires len(underlyingBufRes) >= 4
		// @ requires bytes === underlyingBufRes[:4]
		// @ requires b != nil
		// @ preserves b.Mem(underlyingBufRes)
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
		
		// @ unfold s.scn.ChecksumMem()
		s.Checksum, err = s.scn.computeChecksum(b.Bytes(/*@underlyingBufRes@*/), uint8(L4SCMP))
		if err != nil {
			// @ fold s.scn.ChecksumMem()
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
// @ trusted
// @ requires false
func (s *SCMP) DecodeFromBytes(data []byte, df gopacket.DecodeFeedback) error {
	if size := len(data); size < 4 {
		df.SetTruncated()
		return serrors.New("SCMP layer length is less then 4 bytes", "minimum", 4, "actual", size)
	}
	s.TypeCode = CreateSCMPTypeCode(SCMPType(data[0]), SCMPCode(data[1]))
	s.Checksum = binary.BigEndian.Uint16(data[2:4])
	s.BaseLayer = BaseLayer{Contents: data[:4], Payload: data[4:]}
	return nil
}

// @ trusted
// @ requires false
func (s *SCMP) String() string {
	return fmt.Sprintf("%s(%d)\nPayload: %s", &s.TypeCode, s.Checksum, s.Payload)
}

// SetNetworkLayerForChecksum tells this layer which network layer is wrapping it.
// This is needed for computing the checksum when serializing,
// @ trusted
// @ requires false
func (s *SCMP) SetNetworkLayerForChecksum(l gopacket.NetworkLayer) error {
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

// @ trusted
// @ requires false
func decodeSCMP(data []byte, pb gopacket.PacketBuilder) error {
	scmp := &SCMP{}
	err := scmp.DecodeFromBytes(data, pb)
	if err != nil {
		return err
	}
	pb.AddLayer(scmp)
	return pb.NextDecoder(scmp.NextLayerType())
}
