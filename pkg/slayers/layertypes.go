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

// (VerifiedSCION) To be added on a per-need basis
// @ dup pkgInvariant LayerTypeSCION == 1000
package slayers

import (
	"encoding/binary"
	"strconv"

	"github.com/google/gopacket"
)

var (
	LayerTypeSCION = gopacket.RegisterLayerType(
		1000,
		gopacket.LayerTypeMetadata{
			Name: "SCION",
			Decoder:/*@ gopacket.PromoteDecodeFuncToDecoder( @*/ gopacket.DecodeFunc(decodeSCION /*@ ) @*/),
		},
	)
	LayerClassSCION gopacket.LayerClass = LayerTypeSCION

	LayerTypeSCIONUDP = gopacket.RegisterLayerType(
		1001,
		gopacket.LayerTypeMetadata{
			Name: "SCION/UDP",
			Decoder:/*@ gopacket.PromoteDecodeFuncToDecoder( @*/ gopacket.DecodeFunc(decodeSCIONUDP /*@ ) @*/),
		},
	)
	LayerClassSCIONUDP gopacket.LayerClass = LayerTypeSCIONUDP

	LayerTypeSCMP = gopacket.RegisterLayerType(
		1002,
		gopacket.LayerTypeMetadata{
			Name: "SCMP",
			Decoder:/*@ gopacket.PromoteDecodeFuncToDecoder( @*/ gopacket.DecodeFunc(decodeSCMP /*@ ) @*/),
		},
	)
	LayerClassSCMP gopacket.LayerClass = LayerTypeSCMP

	LayerTypeHopByHopExtn = gopacket.RegisterLayerType(
		1003,
		gopacket.LayerTypeMetadata{
			Name: "HopByHopExtn",
			Decoder:/*@ gopacket.PromoteDecodeFuncToDecoder( @*/ gopacket.DecodeFunc(decodeHopByHopExtn /*@ ) @*/),
		},
	)
	LayerClassHopByHopExtn gopacket.LayerClass = LayerTypeHopByHopExtn

	LayerTypeEndToEndExtn = gopacket.RegisterLayerType(
		1004,
		gopacket.LayerTypeMetadata{
			Name: "EndToEndExtn",
			Decoder:/*@ gopacket.PromoteDecodeFuncToDecoder( @*/ gopacket.DecodeFunc(decodeEndToEndExtn /*@ ) @*/),
		},
	)
	LayerClassEndToEndExtn gopacket.LayerClass = LayerTypeEndToEndExtn

	LayerTypeSCMPExternalInterfaceDown = gopacket.RegisterLayerType(
		1005,
		gopacket.LayerTypeMetadata{
			Name: "SCMPExternalInterfaceDown",
			Decoder:/*@ gopacket.PromoteDecodeFuncToDecoder( @*/ gopacket.DecodeFunc(decodeSCMPExternalInterfaceDown /*@ ) @*/),
		},
	)
	LayerTypeSCMPInternalConnectivityDown = gopacket.RegisterLayerType(
		1006,
		gopacket.LayerTypeMetadata{
			Name: "SCMPInternalConnectivityDown",
			Decoder:/*@ gopacket.PromoteDecodeFuncToDecoder( @*/ gopacket.DecodeFunc(decodeSCMPInternalConnectivityDown /*@ ) @*/),
		},
	)
	LayerTypeSCMPParameterProblem = gopacket.RegisterLayerType(
		1007,
		gopacket.LayerTypeMetadata{
			Name: "SCMPParameterProblem",
			Decoder:/*@ gopacket.PromoteDecodeFuncToDecoder( @*/ gopacket.DecodeFunc(decodeSCMPParameterProblem /*@ ) @*/),
		},
	)
	LayerTypeSCMPDestinationUnreachable = gopacket.RegisterLayerType(
		1008,
		gopacket.LayerTypeMetadata{
			Name: "SCMPDestinationUnreachable",
			Decoder:/*@ gopacket.PromoteDecodeFuncToDecoder( @*/ gopacket.DecodeFunc(decodeSCMPDestinationUnreachable /*@ ) @*/),
		},
	)
	LayerTypeSCMPPacketTooBig = gopacket.RegisterLayerType(
		1009,
		gopacket.LayerTypeMetadata{
			Name: "SCMPPacketTooBig",
			Decoder:/*@ gopacket.PromoteDecodeFuncToDecoder( @*/ gopacket.DecodeFunc(decodeSCMPPacketTooBig /*@ ) @*/),
		},
	)
	LayerTypeSCMPEcho = gopacket.RegisterLayerType(
		1128,
		gopacket.LayerTypeMetadata{
			Name: "SCMPEcho",
			Decoder:/*@ gopacket.PromoteDecodeFuncToDecoder( @*/ gopacket.DecodeFunc(decodeSCMPEcho /*@ ) @*/),
		},
	)
	LayerTypeSCMPTraceroute = gopacket.RegisterLayerType(
		1130,
		gopacket.LayerTypeMetadata{
			Name: "SCMPTraceroute",
			Decoder:/*@ gopacket.PromoteDecodeFuncToDecoder( @*/ gopacket.DecodeFunc(decodeSCMPTraceroute /*@ ) @*/),
		},
	)

	EndpointUDPPort = gopacket.RegisterEndpointType(
		1005,
		gopacket.EndpointTypeMetadata{
			Name: "UDP",
			Formatter: func(b []byte) string {
				return strconv.Itoa(int(binary.BigEndian.Uint16(b)))
			},
		},
	)

	// layerTypeBFD is the identifier for gopacket/layers.LayerTypeBFD.
	// Defining this with a constant here allows to build slayers without linking
	// against gopacket/layers and still allow easily parsing SCION/BFD packets
	// where gopacket/layers is imported.
	layerTypeBFD = gopacket.LayerType(122)
)
