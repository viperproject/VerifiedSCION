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

package scion

import (
	"encoding/binary"
	"fmt"

	"github.com/scionproto/scion/pkg/private/serrors"
	"github.com/scionproto/scion/pkg/slayers/path"
	//@ bit "github.com/scionproto/scion/verification/utils/bitwise"
	//@ . "github.com/scionproto/scion/verification/utils/definitions"
	//@ sl "github.com/scionproto/scion/verification/utils/slices"
)

// MetaLen is the length of the PathMetaHeader.
const MetaLen = 4

const PathType path.Type = 1

// @ requires path.PathPackageMem()
// @ requires !path.Registered(PathType)
// @ ensures  path.PathPackageMem()
// @ ensures  forall t path.Type :: { old(path.Registered(t)) }{ path.Registered(t) } 0 <= t && t < path.MaxPathType ==>
// @ 	t != PathType ==> old(path.Registered(t)) == path.Registered(t)
// @ ensures  path.Registered(PathType)
// @ decreases
func RegisterPath() {
	tmp := path.Metadata{
		Type: PathType,
		Desc: "SCION",
		New:
		//@ ensures p.NonInitMem()
		//@ ensures p != nil
		//@ decreases
		func /*@ newPath @*/ () (p path.Path) {
			rawTmp := &Raw{}
			//@ fold rawTmp.Base.NonInitMem()
			//@ fold rawTmp.NonInitMem()
			return rawTmp
		},
	}
	//@ proof tmp.New implements path.NewPathSpec {
	//@ 	return tmp.New() as newPath
	//@ }
	path.RegisterPath(tmp)
}

// Base holds the basic information that is used by both raw and fully decoded paths.
type Base struct {
	// PathMeta is the SCION path meta header. It is always instantiated when
	// decoding a path from bytes.
	PathMeta MetaHdr
	// NumINF is the number of InfoFields in the path.
	NumINF int
	// NumHops is the number HopFields in the path.
	NumHops int
}

// @ requires  s.NonInitMem()
// @ preserves acc(sl.AbsSlice_Bytes(data, 0, len(data)), R50)
// @ ensures   r != nil ==> (s.NonInitMem() && r.ErrorMem())
// @ ensures   r == nil ==> (
// @ 	s.Mem() &&
// @ 	let lenD := len(data) in
// @ 	MetaLen <= lenD &&
// @ 	let b0 := sl.GetByte(data, 0, lenD, 0) in
// @ 	let b1 := sl.GetByte(data, 0, lenD, 1) in
// @ 	let b2 := sl.GetByte(data, 0, lenD, 2) in
// @ 	let b3 := sl.GetByte(data, 0, lenD, 3) in
// @ 	let line := binary.BigEndian.Uint32Spec(b0, b1, b2, b3) in
// @ 	DecodedFrom(line) == s.GetMetaHdr())
// @ ensures   len(data) < MetaLen ==> r != nil
// @ decreases
func (s *Base) DecodeFromBytes(data []byte) (r error) {
	// PathMeta takes care of bounds check.
	//@ unfold s.NonInitMem()
	err := s.PathMeta.DecodeFromBytes(data)
	if err != nil {
		//@ fold s.NonInitMem()
		return err
	}
	s.NumINF = 0
	s.NumHops = 0

	//@ ghost var metaHdrCpy MetaHdr = s.PathMeta

	//@ invariant -1 <= i && i <= 2
	//@ invariant acc(s)
	//@ invariant metaHdrCpy == s.PathMeta
	//@ invariant 0 <= s.NumHops
	//@ invariant 0 <= s.NumINF && s.NumINF <= 3
	//@ invariant 0 < s.NumINF ==> 0 < s.NumHops
	//@ decreases i
	for i := 2; i >= 0; i-- {
		if s.PathMeta.SegLen[i] == 0 && s.NumINF > 0 {
			e := serrors.New(
				fmt.Sprintf("Meta.SegLen[%d] == 0, but Meta.SegLen[%d] > 0", i, s.NumINF-1))
			//@ fold s.NonInitMem()
			return e
		}
		if s.PathMeta.SegLen[i] > 0 && s.NumINF == 0 {
			s.NumINF = i + 1
		}
		// (VerifiedSCION) Cannot assert bounds of uint:
		// https://github.com/viperproject/gobra/issues/192
		//@ assume int(s.PathMeta.SegLen[i]) >= 0
		s.NumHops += int(s.PathMeta.SegLen[i])
	}
	//@ fold s.Mem()
	return nil
}

// IncPath increases the currHF index and currINF index if appropriate.
// @ requires s.Mem()
// @ ensures  (e != nil) == (
// @ 	old(s.GetNumINF()) == 0 ||
// @ 	old(int(s.GetCurrHF()) >= s.GetNumHops()-1))
// @ ensures  e == nil ==> (
// @ 	s.Mem() &&
// @ 	let oldBase := old(unfolding s.Mem() in *s) in
// @ 	let newBase := (unfolding s.Mem() in *s) in
// @ 	newBase == oldBase.IncPathSpec())
// @ ensures  e != nil ==> (s.NonInitMem() && e.ErrorMem())
// @ decreases
func (s *Base) IncPath() (e error) {
	//@ unfold s.Mem()
	if s.NumINF == 0 {
		//@ fold s.NonInitMem()
		return serrors.New("empty path cannot be increased")
	}
	if int(s.PathMeta.CurrHF) >= s.NumHops-1 {
		s.PathMeta.CurrHF = uint8(s.NumHops - 1)
		//@ fold s.NonInitMem()
		return serrors.New("path already at end")
	}
	s.PathMeta.CurrHF++
	// Update CurrINF
	s.PathMeta.CurrINF = s.infIndexForHF(s.PathMeta.CurrHF)
	//@ fold s.Mem()
	return nil
}

// IsXover returns whether we are at a crossover point.
// @ preserves acc(s.Mem(), R45)
// @ ensures   r == s.IsXoverSpec()
// @ decreases
func (s *Base) IsXover() (r bool) {
	//@ unfold acc(s.Mem(), R45)
	//@ defer fold acc(s.Mem(), R45)
	return s.PathMeta.CurrHF+1 < uint8(s.NumHops) &&
		s.PathMeta.CurrINF != s.infIndexForHF(s.PathMeta.CurrHF+1)
}

// IsFirstHopAfterXover returns whether this is the first hop field after a crossover point.
// @ preserves acc(s.Mem(), R19)
// @ ensures   res ==> unfolding acc(s.Mem(), _) in s.PathMeta.CurrINF > 0 && s.PathMeta.CurrHF > 0
// @ decreases
func (s *Base) IsFirstHopAfterXover() (res bool) {
	//@ unfold acc(s.Mem(), R19)
	//@ defer fold acc(s.Mem(), R19)
	return s.PathMeta.CurrINF > 0 && s.PathMeta.CurrHF > 0 &&
		s.PathMeta.CurrINF-1 == s.infIndexForHF(s.PathMeta.CurrHF-1)
}

// @ preserves acc(s, R50)
// @ ensures   r == s.InfForHfSpec(hf)
// @ decreases
func (s *Base) infIndexForHF(hf uint8) (r uint8) {
	switch {
	case hf < s.PathMeta.SegLen[0]:
		return 0
	case hf < s.PathMeta.SegLen[0]+s.PathMeta.SegLen[1]:
		return 1
	default:
		return 2
	}
}

// Len returns the length of the path in bytes.
// @ pure
// @ requires acc(s.Mem(), _)
// @ ensures  r >= MetaLen
// @ ensures  r == (unfolding acc(s.Mem(), _) in (MetaLen + int(s.NumINF)*path.InfoLen + int(s.NumHops)*path.HopLen))
// @ decreases
func (s *Base) Len() (r int) {
	return /*@ unfolding acc(s.Mem(), _) in @*/ MetaLen + s.NumINF*path.InfoLen + s.NumHops*path.HopLen
}

// Type returns the type of the path.
// @ pure
// @ ensures t == PathType
// @ decreases
func (s *Base) Type() (t path.Type) {
	return PathType
}

// MetaHdr is the PathMetaHdr of a SCION (data-plane) path type.
type MetaHdr struct {
	CurrINF uint8
	CurrHF  uint8
	SegLen  [3]uint8
}

// DecodeFromBytes populates the fields from a raw buffer. The buffer must be of length >=
// scion.MetaLen.
// @ preserves acc(m)
// @ preserves acc(sl.AbsSlice_Bytes(raw, 0, len(raw)), R50)
// @ ensures   (len(raw) >= MetaLen) == (e == nil)
// @ ensures   e == nil ==> (
// @ 	MetaLen <= len(raw)              &&
// @ 	0 <= m.CurrINF && m.CurrINF <= 3 &&
// @ 	0 <= m.CurrHF  && m.CurrHF < 64  &&
// @ 	m.SegsInBounds() &&
// @ 	let lenR := len(raw) in
// @ 	let b0 := sl.GetByte(raw, 0, lenR, 0) in
// @ 	let b1 := sl.GetByte(raw, 0, lenR, 1) in
// @ 	let b2 := sl.GetByte(raw, 0, lenR, 2) in
// @ 	let b3 := sl.GetByte(raw, 0, lenR, 3) in
// @ 	let line := binary.BigEndian.Uint32Spec(b0, b1, b2, b3) in
// @ 	DecodedFrom(line) == *m)
// @ ensures   e != nil ==> e.ErrorMem()
// @ decreases
func (m *MetaHdr) DecodeFromBytes(raw []byte) (e error) {
	if len(raw) < MetaLen {
		// (VerifiedSCION) added cast, otherwise Gobra cannot verify call
		return serrors.New("MetaHdr raw too short", "expected", int(MetaLen), "actual", int(len(raw)))
	}
	//@ unfold acc(sl.AbsSlice_Bytes(raw, 0, len(raw)), R50)
	line := binary.BigEndian.Uint32(raw)
	m.CurrINF = uint8(line >> 30)
	m.CurrHF = uint8(line>>24) & 0x3F
	//@ bit.Shift30LessThan4(line)
	//@ bit.And3fAtMost64(uint8(line>>24))
	m.SegLen[0] = uint8(line>>12) & 0x3F
	m.SegLen[1] = uint8(line>>6) & 0x3F
	m.SegLen[2] = uint8(line) & 0x3F
	//@ bit.And3fAtMost64(uint8(line>>12))
	//@ bit.And3fAtMost64(uint8(line>>6))
	//@ bit.And3fAtMost64(uint8(line))
	//@ fold acc(sl.AbsSlice_Bytes(raw, 0, len(raw)), R50)
	return nil
}

// SerializeTo writes the fields into the provided buffer. The buffer must be of length >=
// scion.MetaLen.
// @ requires  len(b) >= MetaLen
// @ preserves acc(m, R50)
// @ preserves sl.AbsSlice_Bytes(b, 0, len(b))
// @ ensures   e == nil
// @ ensures   let lenR := len(b)           in
// @ 	let b0 := sl.GetByte(b, 0, lenR, 0) in
// @ 	let b1 := sl.GetByte(b, 0, lenR, 1) in
// @ 	let b2 := sl.GetByte(b, 0, lenR, 2) in
// @ 	let b3 := sl.GetByte(b, 0, lenR, 3) in
// @ 	let v  := m.SerializedToLine()      in
// @ 	binary.BigEndian.PutUint32Spec(b0, b1, b2, b3, v)
// @ decreases
func (m *MetaHdr) SerializeTo(b []byte) (e error) {
	if len(b) < MetaLen {
		return serrors.New("buffer for MetaHdr too short", "expected", MetaLen, "actual", len(b))
	}
	line := uint32(m.CurrINF)<<30 | uint32(m.CurrHF&0x3F)<<24
	line |= uint32(m.SegLen[0]&0x3F) << 12
	line |= uint32(m.SegLen[1]&0x3F) << 6
	line |= uint32(m.SegLen[2] & 0x3F)
	//@ unfold acc(sl.AbsSlice_Bytes(b, 0, len(b)))
	binary.BigEndian.PutUint32(b, line)
	//@ fold acc(sl.AbsSlice_Bytes(b, 0, len(b)))
	return nil
}

// @ decreases
func (m MetaHdr) String() string {
	return fmt.Sprintf("{CurrInf: %d, CurrHF: %d, SegLen: %v}", m.CurrINF, m.CurrHF, m.SegLen)
}
