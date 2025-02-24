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

package path

import (
	"encoding/binary"
	"hash"
	//@ . "github.com/scionproto/scion/verification/utils/definitions"
	//@ sl "github.com/scionproto/scion/verification/utils/slices"
	//@ io "verification/io"
)

const MACBufferSize = 16

// MAC calculates the HopField MAC according to
// https://docs.scion.org/en/latest/protocols/scion-header.html#hop-field-mac-computation
// this method does not modify info or hf.
// Modifying the provided buffer after calling this function may change the returned HopField MAC.
// @ requires  h != nil && h.Mem()
// @ preserves len(buffer) >= MACBufferSize ==> sl.Bytes(buffer, 0, len(buffer))
// @ ensures   h.Mem()
// @ decreases
func MAC(h hash.Hash, info InfoField, hf HopField, buffer []byte /*@, ghost as_ io.IO_as @*/) [MacLen]byte {
	mac := FullMAC(h, info, hf, buffer /*@, as_ @*/)
	var res /*@ @ @*/ [MacLen]byte
	//@ unfold sl.Bytes(mac, 0, MACBufferSize)
	copy(res[:], mac[:MacLen] /*@, R1 @*/)
	return res
}

// FullMAC calculates the HopField MAC according to
// https://docs.scion.org/en/latest/protocols/scion-header.html#hop-field-mac-computation
// this method does not modify info or hf.
// Modifying the provided buffer after calling this function may change the returned HopField MAC.
// In contrast to MAC(), FullMAC returns all the 16 bytes instead of only 6 bytes of the MAC.
// @ requires  h != nil && h.Mem()
// @ preserves len(buffer) >= MACBufferSize ==> sl.Bytes(buffer, 0, len(buffer))
// @ ensures   h.Mem()
//
// @ ensures   len(res) == MACBufferSize && sl.Bytes(res, 0, MACBufferSize)
//
// NOTE: It might make sense to use `[:MacLen]` instead of `FromSliceToMacArray`,
// as that is what is ultimately used in `verifyCurrentMAC`.
// @ ensures unfolding sl.Bytes(res, 0, MACBufferSize) in
// @		 let absInf := info.ToAbsInfoField() in
// @		 let absHF := hf.ToIO_HF() in
// @ 		 let absMac := AbsMac(FromSliceToMacArray(res)) in
// @   		 absMac == io.nextMsgtermSpec(as_, absHF.InIF2, absHF.EgIF2, absInf.AInfo, absInf.UInfo)
// @ decreases
// TODO: Test if underscore after as is really necessary
// TODO: think about if it makes sense to have as_ here. In abstraction, we need
// that information in order to get the correct key; in the concrete, the key
// is already encapsulated in hash. Maybe there is a way to relate them
func FullMAC(h hash.Hash, info InfoField, hf HopField, buffer []byte /*@, ghost as_ io.IO_as @*/) (res []byte) {
	if len(buffer) < MACBufferSize {
		buffer = make([]byte, MACBufferSize)
		//@ fold sl.Bytes(buffer, 0, len(buffer))
	}

	h.Reset()
	MACInput(info.SegID, info.Timestamp, hf.ExpTime,
		hf.ConsIngress, hf.ConsEgress, buffer)
	//@ unfold sl.Bytes(buffer, 0, len(buffer))
	//@ defer fold sl.Bytes(buffer, 0, len(buffer))
	// Write must not return an error: https://godoc.org/hash#Hash
	if _, err := h.Write(buffer); err != nil {
		// @ Unreachable()
		panic(err)
	}
	//@ assert h.Size() >= 16
	res = h.Sum(buffer[:0])[:16]

	// NOTE: We could potentially go even further and relate
	// - `io.plaintextToMac` to `MACInput` and
	// - `io.mac(io.macKey(io.asidToKey(as_)), -)` to `h.Write` and `h.Sum`,
	// but that might get messy. In order to verify SIF, it suffices to relate
	// the result here to `io.nextMsgtermSpec`.

	// NOTE: This is our "MAC assumption", linking the abstraction of the
	// concrete MAC tag to the abstract computation of the MAC tag.
	//@ absInf := info.ToAbsInfoField()
	//@ absHF := hf.ToIO_HF()
	//@ absMac := AbsMac(FromSliceToMacArray(res))
	//@ AssumeForIO(absMac == io.nextMsgtermSpec(as_, absHF.InIF2, absHF.EgIF2, absInf.AInfo, absInf. UInfo))

	//@ fold sl.Bytes(res, 0, MACBufferSize)
	return res
}

// MACInput returns the MAC input data block with the following layout:
//
//	 0                   1                   2                   3
//	 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
//	+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//	|               0               |             SegID             |
//	+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//	|                           Timestamp                           |
//	+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//	|       0       |    ExpTime    |          ConsIngress          |
//	+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//	|          ConsEgress           |               0               |
//	+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//
// @ requires  len(buffer) >= MACBufferSize
// @ preserves sl.Bytes(buffer, 0, len(buffer))
// @ decreases
func MACInput(segID uint16, timestamp uint32, expTime uint8,
	consIngress, consEgress uint16, buffer []byte) {
	//@ unfold sl.Bytes(buffer, 0, len(buffer))

	//@ assert &buffer[0:2][0] == &buffer[0] && &buffer[0:2][1] == &buffer[1]
	binary.BigEndian.PutUint16(buffer[0:2], 0)
	//@ assert &buffer[2:4][0] == &buffer[2] && &buffer[2:4][1] == &buffer[3]
	binary.BigEndian.PutUint16(buffer[2:4], segID)
	//@ assert &buffer[4:8][0] == &buffer[4] && &buffer[4:8][1] == &buffer[5]
	//@ assert &buffer[4:8][2] == &buffer[6] && &buffer[4:8][3] == &buffer[7]
	binary.BigEndian.PutUint32(buffer[4:8], timestamp)
	buffer[8] = 0
	buffer[9] = expTime
	//@ assert &buffer[10:12][0] == &buffer[10] && &buffer[10:12][1] == &buffer[11]
	binary.BigEndian.PutUint16(buffer[10:12], consIngress)
	//@ assert &buffer[12:14][0] == &buffer[12] && &buffer[12:14][1] == &buffer[13]
	binary.BigEndian.PutUint16(buffer[12:14], consEgress)
	//@ assert &buffer[14:16][0] == &buffer[14] && &buffer[14:16][1] == &buffer[15]
	binary.BigEndian.PutUint16(buffer[14:16], 0)
	//@ fold sl.Bytes(buffer, 0, len(buffer))
}
