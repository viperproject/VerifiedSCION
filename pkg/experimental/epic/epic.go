// Copyright 2020 ETH Zurich
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

package epic

import (
	"crypto/aes"
	"crypto/cipher"
	"crypto/subtle"
	"encoding/binary"
	"math"
	"time"

	"github.com/scionproto/scion/pkg/addr"
	"github.com/scionproto/scion/pkg/private/serrors"
	"github.com/scionproto/scion/pkg/slayers"
	"github.com/scionproto/scion/pkg/slayers/path/epic"
	// @ . "github.com/scionproto/scion/verification/utils/definitions"
	// @ sl "github.com/scionproto/scion/verification/utils/slices"
)

const (
	// AuthLen denotes the size of the authenticator in bytes
	AuthLen = 16
	// MaxPacketLifetime denotes the maximal lifetime of a packet
	MaxPacketLifetime time.Duration = 2 * time.Second
	// MaxClockSkew denotes the maximal clock skew
	MaxClockSkew time.Duration = time.Second
	// TimestampResolution denotes the resolution of the epic timestamp
	TimestampResolution = 21 * time.Microsecond
	// MACBufferSize denotes the buffer size of the CBC input and output.
	MACBufferSize = 48
)

var zeroInitVector /*@@@*/ [16]byte

// CreateTimestamp returns the epic timestamp, which encodes the current time (now) relative to the
// input timestamp. The input timestamp must not be in the future (compared to the current time),
// otherwise an error is returned. An error is also returned if the current time is more than 1 day
// and 63 minutes after the input timestamp.
// @ ensures err != nil ==> err.ErrorMem()
// @ decreases
func CreateTimestamp(input time.Time, now time.Time) (res uint32, err error) {
	if input.After(now) {
		return 0, serrors.New("provided input timestamp is in the future",
			"input", input, "now", now)
	}
	epicTS := now.Sub(input)/TimestampResolution - 1
	if epicTS < 0 {
		epicTS = 0
	}
	if epicTS >= (1 << 32) {
		return 0, serrors.New("diff between input and now >1d63min", "epicTS", epicTS)
	}
	return uint32(epicTS), nil
}

// VerifyTimestamp checks whether an EPIC packet is fresh. This means that the time the packet
// was sent from the source host, which is encoded by the timestamp and the epicTimestamp,
// does not date back more than the maximal packet lifetime of two seconds. The function also takes
// a possible clock drift between the packet source and the verifier of up to one second into
// account.
// @ ensures err != nil ==> err.ErrorMem()
// @ decreases
func VerifyTimestamp(timestamp time.Time, epicTS uint32, now time.Time) (err error) {
	diff := (time.Duration(epicTS) + 1) * TimestampResolution
	tsSender := timestamp.Add(diff)

	if tsSender.After(now.Add(MaxClockSkew)) {
		delta := tsSender.Sub(now.Add(MaxClockSkew))
		return serrors.New("epic timestamp is in the future",
			"delta", delta)
	}
	if now.After(tsSender.Add(MaxPacketLifetime).Add(MaxClockSkew)) {
		delta := now.Sub(tsSender.Add(MaxPacketLifetime).Add(MaxClockSkew))
		return serrors.New("epic timestamp expired",
			"delta", delta)
	}
	return nil
}

// CalcMac derives the EPIC MAC (PHVF/LHVF) given the full 16 bytes of the SCION path type
// MAC (auth), the EPIC packet ID (pktID), the timestamp in the Info Field (timestamp),
// and the SCION common/address header (s).
// If the same buffer is provided in subsequent calls to this function, the previously returned
// EPIC MAC may get overwritten. Only the most recently returned EPIC MAC is guaranteed to be
// valid.
// @ requires  len(auth) == 16
// @ requires  sl.Bytes(buffer, 0, len(buffer))
// @ preserves acc(s.Mem(ub), R20)
// @ preserves acc(sl.Bytes(ub, 0, len(ub)), R20)
// @ preserves acc(sl.Bytes(auth, 0, len(auth)), R30)
// @ ensures   reserr == nil ==> sl.Bytes(res, 0, len(res))
// @ ensures   reserr == nil ==> (sl.Bytes(res, 0, len(res)) --* sl.Bytes(buffer, 0, len(buffer)))
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// @ ensures   reserr != nil ==> sl.Bytes(buffer, 0, len(buffer))
// @ decreases
func CalcMac(auth []byte, pktID epic.PktID, s *slayers.SCION,
	timestamp uint32, buffer []byte /*@ , ghost ub []byte @*/) (res []byte, reserr error) {

	// @ ghost oldBuffer := buffer
	// @ ghost allocatesNewBuffer := len(buffer) < MACBufferSize
	if len(buffer) < MACBufferSize {
		buffer = make([]byte, MACBufferSize)
		// @ fold sl.Bytes(buffer, 0, len(buffer))
	}

	// Initialize cryptographic MAC function
	f, err := initEpicMac(auth)
	if err != nil {
		return nil, err
	}
	// Prepare the input for the MAC function
	inputLength, err := prepareMacInput(pktID, s, timestamp, buffer /*@, ub @*/)
	if err != nil {
		return nil, err
	}
	// @ assert 16 <= inputLength
	// @ assert f.BlockSize() == 16
	// Calculate Epic MAC = first 4 bytes of the last CBC block
	// @ sl.SplitRange_Bytes(buffer, 0, inputLength, writePerm)
	input := buffer[:inputLength]
	f.CryptBlocks(input, input)
	// @ ghost start := len(input)-f.BlockSize()
	// @ ghost end   := start + 4
	result := input[len(input)-f.BlockSize() : len(input)-f.BlockSize()+4]
	// @ sl.SplitRange_Bytes(input, start, end, writePerm)
	// @ package (sl.Bytes(result, 0, len(result)) --* sl.Bytes(oldBuffer, 0, len(oldBuffer))) {
	// @ 	ghost if !allocatesNewBuffer {
	// @ 		assert oldBuffer === buffer
	// @ 		sl.CombineRange_Bytes(input, start, end, writePerm)
	// @ 		sl.CombineRange_Bytes(oldBuffer, 0, inputLength, writePerm)
	// @ 	}
	// @ }
	// @ assert (sl.Bytes(result, 0, len(result)) --* sl.Bytes(oldBuffer, 0, len(oldBuffer)))
	return result, nil
}

// VerifyHVF verifies the correctness of the HVF (PHVF or the LHVF) field in the EPIC packet by
// recalculating and comparing it. If the EPIC authenticator (auth), which denotes the full 16
// bytes of the SCION path type MAC, has invalid length, or if the MAC calculation gives an error,
// also VerifyHVF returns an error. The verification was successful if and only if VerifyHVF
// returns nil.
// @ preserves sl.Bytes(buffer, 0, len(buffer))
// @ preserves acc(s.Mem(ub), R20)
// @ preserves acc(sl.Bytes(hvf, 0, len(hvf)), R50)
// @ preserves acc(sl.Bytes(ub, 0, len(ub)), R20)
// @ preserves acc(sl.Bytes(auth, 0, len(auth)), R30)
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// @ decreases
func VerifyHVF(auth []byte, pktID epic.PktID, s *slayers.SCION,
	timestamp uint32, hvf []byte, buffer []byte /*@ , ghost ub []byte @*/) (reserr error) {

	if s == nil || len(auth) != AuthLen {
		return serrors.New("invalid input")
	}

	mac, err := CalcMac(auth, pktID, s, timestamp, buffer /*@ , ub @*/)
	if err != nil {
		return err
	}

	if subtle.ConstantTimeCompare(hvf, mac) == 0 {
		// @ apply sl.Bytes(mac, 0, len(mac)) --* sl.Bytes(buffer, 0, len(buffer))
		return serrors.New("epic hop validation field verification failed",
			"hvf in packet", hvf, "calculated mac", mac, "auth", auth)
	}
	// @ apply sl.Bytes(mac, 0, len(mac)) --* sl.Bytes(buffer, 0, len(buffer))
	return nil
}

// PktCounterFromCore creates a counter for the packet identifier
// based on the core ID and the core counter.
func PktCounterFromCore(coreID uint8, coreCounter uint32) uint32 {
	return (uint32(coreID) << 24) | (coreCounter & 0x00FFFFFF)
}

// CoreFromPktCounter reads the core ID and the core counter
// from a counter belonging to a packet identifier.
func CoreFromPktCounter(counter uint32) (uint8, uint32) {
	coreID := uint8(counter >> 24)
	coreCounter := counter & 0x00FFFFFF
	return coreID, coreCounter
}

// @ requires  len(key) == 16
// @ preserves acc(sl.Bytes(key, 0, len(key)), R50)
// @ ensures   reserr == nil ==>
// @ 	res != nil && res.Mem() && res.BlockSize() == 16
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// @ decreases
func initEpicMac(key []byte) (res cipher.BlockMode, reserr error) {
	block, err := aes.NewCipher(key)
	if err != nil {
		return nil, serrors.New("Unable to initialize AES cipher")
	}

	// @ establishPostInitInvariant()
	// @ unfold acc(postInitInvariant(), _)
	// CBC-MAC = CBC-Encryption with zero initialization vector
	mode := cipher.NewCBCEncrypter(block, zeroInitVector[:])
	return mode, nil
}

// @ requires  MACBufferSize <= len(inputBuffer)
// @ preserves acc(s.Mem(ub), R20)
// @ preserves acc(sl.Bytes(ub, 0, len(ub)), R20)
// @ preserves sl.Bytes(inputBuffer, 0, len(inputBuffer))
// @ ensures   reserr == nil ==> 16 <= res && res <= len(inputBuffer)
// @ ensures   reserr != nil ==> reserr.ErrorMem()
// @ decreases
func prepareMacInput(pktID epic.PktID, s *slayers.SCION, timestamp uint32,
	inputBuffer []byte /*@ , ghost ub []byte @*/) (res int, reserr error) {
	// @ share pktID

	//   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
	//   | flags (1B) | timestamp (4B) |    packet ID (8B)     |
	//   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
	//   | srcIA (8B) | srcAddr (4/8/12/16B) | payloadLen (2B) |
	//   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
	//   | zero padding (0-15B)                                |
	//   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
	// The "flags" field only encodes the length of the source address.

	if s == nil {
		return 0, serrors.New("SCION common+address header must not be nil")
	}
	// @ unfold acc(s.Mem(ub), R20/2)
	// @ defer fold acc(s.Mem(ub), R20/2)
	// @ unfold acc(s.HeaderMem(ub[slayers.CmnHdrLen:]), R20/2)
	// @ defer fold acc(s.HeaderMem(ub[slayers.CmnHdrLen:]), R20/2)
	srcAddr := s.RawSrcAddr
	// @ ghost start := slayers.CmnHdrLen+2*addr.IABytes+s.DstAddrType.Length()
	// @ ghost end := slayers.CmnHdrLen+2*addr.IABytes+s.DstAddrType.Length()+s.SrcAddrType.Length()
	// @ assert srcAddr === ub[start:end]
	l := len(srcAddr)

	// Calculate a multiple of 16 such that the input fits in
	nrBlocks := int(math.Ceil((float64(23) + float64(l)) / float64(16)))
	// (VerifiedSCION) The following assumptions cannot be currently proven due to Gobra's incomplete
	// support for floats.
	// @ assume 23 + l <= nrBlocks * 16
	// @ assume nrBlocks * 16 <= 23 + l + 16
	inputLength := 16 * nrBlocks

	// Fill input
	// @ unfold sl.Bytes(inputBuffer, 0, len(inputBuffer))
	offset := 0
	inputBuffer[0] = uint8(s.SrcAddrType & 0x3) // extract length bits
	offset += 1
	// @ assert forall i int :: { &inputBuffer[offset:][i] } 0 <= i && i < len(inputBuffer[offset:]) ==>
	// @ 	&inputBuffer[offset:][i] == &inputBuffer[offset+i]
	binary.BigEndian.PutUint32(inputBuffer[offset:], timestamp)
	offset += 4
	// @ fold sl.Bytes(inputBuffer, 0, len(inputBuffer))
	// @ sl.SplitRange_Bytes(inputBuffer, offset, len(inputBuffer), writePerm)
	pktID.SerializeTo(inputBuffer[offset:])
	// @ sl.CombineRange_Bytes(inputBuffer, offset, len(inputBuffer), writePerm)
	offset += epic.PktIDLen
	// @ unfold sl.Bytes(inputBuffer, 0, len(inputBuffer))
	// @ assert forall i int :: { &inputBuffer[offset:][i] } 0 <= i && i < len(inputBuffer[offset:]) ==>
	// @ 	&inputBuffer[offset:][i] == &inputBuffer[offset+i]
	binary.BigEndian.PutUint64(inputBuffer[offset:], uint64(s.SrcIA))
	offset += addr.IABytes
	// @ assert forall i int :: { &inputBuffer[offset:][i] } 0 <= i && i < len(inputBuffer[offset:]) ==>
	// @ 	&inputBuffer[offset:][i] == &inputBuffer[offset+i]
	// @ sl.SplitRange_Bytes(ub, start, end, R20)
	// @ unfold acc(sl.Bytes(srcAddr, 0, len(srcAddr)), R20)
	copy(inputBuffer[offset:], srcAddr /*@ , R20 @*/)
	// @ fold acc(sl.Bytes(srcAddr, 0, len(srcAddr)), R20)
	// @ sl.CombineRange_Bytes(ub, start, end, R20)
	offset += l
	// @ assert forall i int :: { &inputBuffer[offset:][i] } 0 <= i && i < len(inputBuffer[offset:]) ==>
	// @ 	&inputBuffer[offset:][i] == &inputBuffer[offset+i]
	binary.BigEndian.PutUint16(inputBuffer[offset:], s.PayloadLen)
	offset += 2
	// @ assert offset == 23 + l
	// @ assert offset <= inputLength
	// @ assert inputLength <= len(inputBuffer)
	// @ assert forall i int :: { &inputBuffer[offset:inputLength][i] } 0 <= i && i < len(inputBuffer[offset:inputLength]) ==>
	// @ 	&inputBuffer[offset:inputLength][i] == &inputBuffer[offset+i]
	// @ assert forall i int :: { &inputBuffer[offset:inputLength][i] } 0 <= i && i < len(inputBuffer[offset:inputLength]) ==>
	// @ 	acc(&inputBuffer[offset:inputLength][i])
	// @ establishPostInitInvariant()
	// @ unfold acc(postInitInvariant(), _)
	// @ assert acc(sl.Bytes(zeroInitVector[:], 0, 16), _)
	// (VerifiedSCION) From the pkg invariant, we learn that we have a wildcard access to zeroInitVector.
	// Unfortunately, it is not possible to call `copy` with a wildcard amount, even though
	// that would be perfectly fine. The spec of `copy` would need to be adapted to allow for that case.
	// @ inhale acc(sl.Bytes(zeroInitVector[:], 0, len(zeroInitVector[:])), R55)
	// @ unfold acc(sl.Bytes(zeroInitVector[:], 0, len(zeroInitVector[:])), R55)
	// @ assert forall i int :: { &zeroInitVector[:][i] } 0 <= i && i < len(zeroInitVector[:]) ==>
	// @ 	&zeroInitVector[:][i] == &zeroInitVector[i]
	copy(inputBuffer[offset:inputLength], zeroInitVector[:] /*@ , R55 @*/)
	// @ fold sl.Bytes(inputBuffer, 0, len(inputBuffer))
	return inputLength, nil
}
