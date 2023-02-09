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
	"github.com/scionproto/scion/pkg/private/serrors"
	"github.com/scionproto/scion/pkg/slayers/path"
	//@ def "github.com/scionproto/scion/verification/utils/definitions"
	//@ "github.com/scionproto/scion/verification/utils/definitions"
	//@ "github.com/scionproto/scion/verification/utils/slices"
)

const (
	// MaxINFs is the maximum number of info fields in a SCION path.
	MaxINFs = 3
	// MaxHops is the maximum number of hop fields in a SCION path.
	MaxHops = 64
)

// Decoded implements the SCION (data-plane) path type. Decoded is intended to be used in
// non-performance critical code paths, where the convenience of having a fully parsed path trumps
// the loss of performance.
type Decoded struct {
	Base
	// InfoFields contains all the InfoFields of the path.
	InfoFields []path.InfoField
	// HopFields contains all the HopFields of the path.
	HopFields []path.HopField
}

// DecodeFromBytes fully decodes the SCION path into the corresponding fields.
// @ requires  s.NonInitMem()
// @ preserves slices.AbsSlice_Bytes(data, 0, len(data))
// @ ensures   r == nil ==> len(data) > 0
// @ ensures   r == nil ==> s.Mem(data)
// @ ensures   r == nil ==> (unfolding s.Mem(data) in unfolding s.Base.Mem() in unfolding slices.AbsSlice_Bytes(data, 0, len(data)) in s.PathMeta.CurrINF == data[0] >> 6 && s.NumINF == s.Base.NumINFValue())
// @ ensures   r != nil ==> (r.ErrorMem() && s.NonInitMem())
// @ decreases
func (s *Decoded) DecodeFromBytes(data []byte) (r error) {
	//@ unfold s.NonInitMem()
	if err := s.Base.DecodeFromBytes(data); err != nil {
		//@ fold s.NonInitMem()
		return err
	}
	// (VerifiedSCION) Gobra expects a stronger contract for s.Len() when in fact
	// what happens here is that we just call the same function in s.Base.
	if minLen := s. /*@ Base. @*/ Len(); len(data) < minLen {
		//@ apply s.Base.Mem() --* s.Base.NonInitMem()
		//@ fold s.NonInitMem()
		return serrors.New("DecodedPath raw too short", "expected", minLen, "actual", int(len(data)))
	}
	offset := MetaLen
	s.InfoFields = make([]path.InfoField, ( /*@ unfolding s.Base.Mem() in @*/ s.NumINF))
	//@ assert len(data) >= MetaLen + s.Base.getNumINF() * path.InfoLen + s.Base.getNumHops() * path.HopLen
	//@ slices.SplitByIndex_Bytes(data, 0, len(data), offset, definitions.ReadL1)

	//@ invariant acc(&s.InfoFields)
	//@ invariant acc(s.Base.Mem(), definitions.ReadL1)
	//@ invariant len(s.InfoFields) == s.Base.getNumINF()
	//@ invariant 0 <= i && i <= s.Base.getNumINF()
	//@ invariant len(data) >= MetaLen + s.Base.getNumINF() * path.InfoLen + s.Base.getNumHops() * path.HopLen
	//@ invariant offset == MetaLen + i * path.InfoLen
	//@ invariant forall j int :: 0 <= j && j < s.Base.getNumINF() ==> acc(&s.InfoFields[j])
	//@ invariant acc(slices.AbsSlice_Bytes(data, 0, offset), definitions.ReadL1)
	//@ invariant acc(slices.AbsSlice_Bytes(data, offset, len(data)), definitions.ReadL1)
	//@ decreases s.Base.getNumINF() - i
	for i := 0; i < /*@ unfolding acc(s.Base.Mem(), _) in @*/ s.NumINF; i++ {
		//@ slices.SplitByIndex_Bytes(data, offset, len(data), offset + path.InfoLen, definitions.ReadL1)
		//@ slices.Reslice_Bytes(data, offset, offset + path.InfoLen, definitions.ReadL1)
		if err := s.InfoFields[i].DecodeFromBytes(data[offset : offset+path.InfoLen]); err != nil {
			// (VerifiedSCION) infofield.DecodeFromBytes guarantees that err == nil.
			// Thus, this branch is not reachable.
			return err
		}
		//@ assert len(data[offset:offset+path.InfoLen]) == path.InfoLen
		//@ slices.Unslice_Bytes(data, offset, offset + path.InfoLen, definitions.ReadL1)
		//@ slices.CombineAtIndex_Bytes(data, 0, offset + path.InfoLen, offset, definitions.ReadL1)
		offset += path.InfoLen
	}
	s.HopFields = make([]path.HopField, ( /*@ unfolding s.Base.Mem() in @*/ s.NumHops))
	//@ invariant acc(&s.HopFields)
	//@ invariant acc(s.Base.Mem(), definitions.ReadL1)
	//@ invariant len(s.HopFields) == s.Base.getNumHops()
	//@ invariant 0 <= i && i <= s.Base.getNumHops()
	//@ invariant forall j int :: i <= j && j < s.Base.getNumHops() ==> acc(&s.HopFields[j])
	//@ invariant forall j int :: 0 <= j && j < i ==> s.HopFields[j].Mem()
	//@ invariant len(data) >= MetaLen + s.Base.getNumINF() * path.InfoLen + s.Base.getNumHops() * path.HopLen
	//@ invariant offset == MetaLen + s.Base.getNumINF() * path.InfoLen + i * path.HopLen
	//@ invariant acc(slices.AbsSlice_Bytes(data, 0, offset), definitions.ReadL1)
	//@ invariant acc(slices.AbsSlice_Bytes(data, offset, len(data)), definitions.ReadL1)
	//@ decreases s.Base.getNumHops() - i
	for i := 0; i < /*@ unfolding acc(s.Base.Mem(), definitions.ReadL2) in @*/ s.NumHops; i++ {
		//@ slices.SplitByIndex_Bytes(data, offset, len(data), offset + path.HopLen, definitions.ReadL1)
		//@ slices.Reslice_Bytes(data, offset, offset + path.HopLen, definitions.ReadL1)
		if err := s.HopFields[i].DecodeFromBytes(data[offset : offset+path.HopLen]); err != nil {
			// (VerifiedSCION) infofield.DecodeFromBytes guarantees that err == nil.
			// Thus, this branch should not be reachable.
			return err
		}
		//@ assert len(data[offset:offset+path.HopLen]) == path.HopLen
		//@ slices.Unslice_Bytes(data, offset, offset + path.HopLen, definitions.ReadL1)
		//@ slices.CombineAtIndex_Bytes(data, 0, offset + path.HopLen, offset, definitions.ReadL1)
		offset += path.HopLen
	}
	//@ slices.CombineAtIndex_Bytes(data, 0, len(data), offset, definitions.ReadL1)
	//@ fold s.Mem(data)
	return nil
}

// SerializeTo writePerms the path to a slice. The slice must be big enough to hold the entire data,
// otherwise an error is returned.
// @ preserves acc(s.Mem(ubuf), def.ReadL1)
// @ preserves slices.AbsSlice_Bytes(ubuf, 0, len(ubuf))
// @ preserves b !== ubuf ==> slices.AbsSlice_Bytes(b, 0, len(b))
// @ ensures   r != nil ==> r.ErrorMem()
// @ decreases
func (s *Decoded) SerializeTo(b []byte /*@, ghost ubuf []byte @*/) (r error) {
	if len(b) < s.Len( /*@ ubuf @*/ ) {
		return serrors.New("buffer too small to serialize path.", "expected", s.Len( /*@ ubuf @*/ ),
			"actual", len(b))
	}
	//@ unfold acc(s.Mem(ubuf), def.ReadL1)
	//@ assert slices.AbsSlice_Bytes(b, 0, len(b))
	//@ slices.SplitByIndex_Bytes(b, 0, len(b), MetaLen, writePerm)
	//@ slices.Reslice_Bytes(b, 0, MetaLen, writePerm)
	//@ unfold acc(s.Base.Mem(), def.ReadL1)
	if err := s.PathMeta.SerializeTo(b[:MetaLen]); err != nil {
		// @ definitions.Unreachable()
		return err
	}
	//@ fold acc(s.Base.Mem(), def.ReadL1)
	//@ slices.Unslice_Bytes(b, 0, MetaLen, writePerm)
	//@ slices.CombineAtIndex_Bytes(b, 0, len(b), MetaLen, writePerm)
	//@ fold acc(s.Mem(ubuf), def.ReadL1)
	offset := MetaLen

	//@ invariant acc(s.Mem(ubuf), def.ReadL1)
	//@ invariant slices.AbsSlice_Bytes(ubuf, 0, len(ubuf))
	//@ invariant b !== ubuf ==> slices.AbsSlice_Bytes(b, 0, len(b))
	//@ invariant s.Len(ubuf) <= len(b)
	//@ invariant 0 <= i && i <= s.getLenInfoFields(ubuf)
	//@ invariant offset == MetaLen + i * path.InfoLen
	//@ invariant MetaLen + s.getLenInfoFields(ubuf) * path.InfoLen + s.getLenHopFields(ubuf) * path.HopLen <= len(b)
	//@ decreases s.getLenInfoFields(ubuf) - i
	// (VerifiedSCION) TODO: reinstate the original range clause
	// for _, info := range s.InfoFields {
	for i := 0; i < /*@ unfolding acc(s.Mem(ubuf), _) in @*/ len(s.InfoFields); i++ {
		//@ unfold acc(s.Mem(ubuf), def.ReadL1)
		info := &s.InfoFields[i]
		//@ slices.SplitByIndex_Bytes(b, 0, len(b), offset, writePerm)
		//@ slices.SplitByIndex_Bytes(b, offset, len(b), offset + path.InfoLen, writePerm)
		//@ slices.Reslice_Bytes(b, offset, offset + path.InfoLen, writePerm)
		//@ assert slices.AbsSlice_Bytes(b[offset:offset+path.InfoLen], 0, path.InfoLen)
		if err := info.SerializeTo(b[offset : offset+path.InfoLen]); err != nil {
			//@ def.Unreachable()
			return err
		}
		//@ slices.Unslice_Bytes(b, offset, offset + path.InfoLen, writePerm)
		//@ slices.CombineAtIndex_Bytes(b, offset, len(b), offset + path.InfoLen, writePerm)
		//@ slices.CombineAtIndex_Bytes(b, 0, len(b), offset, writePerm)
		//@ fold acc(s.Mem(ubuf), def.ReadL1)
		offset += path.InfoLen
	}
	//@ invariant acc(s.Mem(ubuf), def.ReadL1)
	//@ invariant slices.AbsSlice_Bytes(ubuf, 0, len(ubuf))
	//@ invariant b !== ubuf ==> slices.AbsSlice_Bytes(b, 0, len(b))
	//@ invariant s.Len(ubuf) <= len(b)
	//@ invariant 0 <= i && i <= s.getLenHopFields(ubuf)
	//@ invariant offset == MetaLen + s.getLenInfoFields(ubuf) * path.InfoLen + i * path.HopLen
	//@ invariant MetaLen + s.getLenInfoFields(ubuf) * path.InfoLen + s.getLenHopFields(ubuf) * path.HopLen <= len(b)
	//@ decreases s.getLenHopFields(ubuf)-i
	// (VerifiedSCION) TODO: reinstate the original range clause
	// for _, hop := range s.HopFields {
	for i := 0; i < /*@ unfolding acc(s.Mem(ubuf), _) in @*/ len(s.HopFields); i++ {
		//@ unfold acc(s.Mem(ubuf), def.ReadL1)
		hop := &s.HopFields[i]
		//@ slices.SplitByIndex_Bytes(b, 0, len(b), offset, writePerm)
		//@ slices.SplitByIndex_Bytes(b, offset, len(b), offset + path.HopLen, writePerm)
		//@ slices.Reslice_Bytes(b, offset, offset + path.HopLen, writePerm)
		if err := hop.SerializeTo(b[offset : offset+path.HopLen]); err != nil {
			//@ def.Unreachable()
			return err
		}
		//@ slices.Unslice_Bytes(b, offset, offset + path.HopLen, writePerm)
		//@ slices.CombineAtIndex_Bytes(b, offset, len(b), offset + path.HopLen, writePerm)
		//@ slices.CombineAtIndex_Bytes(b, 0, len(b), offset, writePerm)
		//@ fold acc(s.Mem(ubuf), def.ReadL1)
		offset += path.HopLen
	}
	return nil
}

// Reverse reverses a SCION path.
// @ requires s.Mem(ubuf)
// @ ensures  r == nil ==> p != nil
// @ ensures  r == nil ==> p.Mem(ubuf)
// @ ensures  r == nil ==> p == s
// @ ensures  r == nil ==> typeOf(p) == type[*Decoded]
// @ ensures  r == nil && old(unfolding s.Mem(ubuf) in s.Base.InfValid()) ==> unfolding (p.(*Decoded)).Mem(ubuf) in (p.(*Decoded)).Base.InfValid()
// @ ensures  r != nil ==> r.ErrorMem() && s.Mem(ubuf)
// @ decreases
func (s *Decoded) Reverse( /*@ ghost ubuf []byte @*/ ) (p path.Path, r error) {
	//@ unfold s.Mem(ubuf)
	//@ unfold s.Base.Mem()
	if s.NumINF == 0 {
		//@ fold s.Base.Mem()
		//@ fold s.Mem(ubuf)
		return nil, serrors.New("empty decoded path is invalid and cannot be reversed")
	}
	//@ fold s.Base.Mem()
	//@ fold s.Mem(ubuf)
	// Reverse order of InfoFields and SegLens
	//@ invariant s.Mem(ubuf)
	//@ invariant old(unfolding s.Mem(ubuf) in s.Base.InfValid()) ==> unfolding s.Mem(ubuf) in s.Base.InfValid()
	//@ invariant 0 <= i && i < unfolding s.Mem(ubuf) in (unfolding s.Base.Mem() in s.NumINF)
	//@ invariant 0 <= j && j < unfolding s.Mem(ubuf) in (unfolding s.Base.Mem() in s.NumINF)
	//@ decreases j-i
	for i, j := 0, ( /*@ unfolding s.Mem(ubuf) in (unfolding s.Base.Mem() in @*/ s.NumINF - 1 /*@) @*/); i < j; i, j = i+1, j-1 {
		//@ unfold s.Mem(ubuf)
		s.InfoFields[i], s.InfoFields[j] = s.InfoFields[j], s.InfoFields[i]
		//@ requires s.Base.Mem()
		//@ requires 0 <= i && i < unfolding s.Base.Mem() in s.NumINF
		//@ requires 0 <= j && j < unfolding s.Base.Mem() in s.NumINF
		//@ ensures  s.Base.Mem()
		//@ ensures  s.Base.getNumINF() == before(s.Base.getNumINF())
		//@ ensures  s.Base.getNumHops() == before(s.Base.getNumHops())
		//@ ensures  before(s.Base.InfValid()) ==> s.Base.InfValid()
		//@ decreases
		//@ outline (
		//@ unfold s.Base.Mem()
		s.PathMeta.SegLen[i], s.PathMeta.SegLen[j] = s.PathMeta.SegLen[j], s.PathMeta.SegLen[i]
		//@ fold s.Base.Mem()
		//@ )
		//@ fold s.Mem(ubuf)
	}
	//@ preserves s.Mem(ubuf)
	//@ ensures before(unfolding s.Mem(ubuf) in s.Base.InfValid()) ==> unfolding s.Mem(ubuf) in s.Base.InfValid()
	//@ decreases
	//@ outline(
	//@ unfold s.Mem(ubuf)
	//@ invariant acc(s.Base.Mem(), definitions.ReadL10)
	//@ invariant 0 <= i && i <= s.getNumINF()
	//@ invariant acc(&s.InfoFields, definitions.ReadL10)
	//@ invariant len(s.InfoFields) == s.getNumINF()
	//@ invariant forall i int :: 0 <= i && i < len(s.InfoFields) ==> (acc(&s.InfoFields[i].ConsDir))
	//@ decreases MaxINFs-i
	// Reverse cons dir flags
	for i := 0; i < ( /*@ unfolding acc(s.Base.Mem(), definitions.ReadL11) in @*/ s.NumINF); i++ {
		info := &s.InfoFields[i]
		info.ConsDir = !info.ConsDir
	}
	//@ fold s.Mem(ubuf)
	//@ )

	// (VerifiedSCION) we are fairly confident of the correctness of this loop.
	// Unfortunately, Gobra cannot prove it in a timely fashion.
	//@ trusted
	//@ preserves s.Mem(ubuf)
	//@ ensures before(unfolding s.Mem(ubuf) in s.Base.InfValid()) ==> unfolding s.Mem(ubuf) in s.Base.InfValid()
	//@ decreases
	//@ outline(
	// Reverse order of hop fields
	//@ invariant s.Mem(ubuf)
	//@ invariant 0 <= i && i <= unfolding s.Mem(ubuf) in s.getNumHops()
	//@ invariant -1 <= j && j < unfolding s.Mem(ubuf) in s.getNumHops()
	//@ decreases j-i
	for i, j := 0, ( /*@ unfolding s.Mem(ubuf) in (unfolding s.Base.Mem() in @*/ s.NumHops - 1 /*@ ) @*/); i < j; i, j = i+1, j-1 {
		//@ unfold s.Mem(ubuf)
		//@ assert &s.HopFields[i] != &s.HopFields[j]
		//@ unfold s.HopFields[i].Mem()
		//@ unfold s.HopFields[j].Mem()
		//@ assert acc(&s.HopFields[i]) && acc(&s.HopFields[j])
		s.HopFields[i], s.HopFields[j] = s.HopFields[j], s.HopFields[i]
		//@ assert acc(&s.HopFields[i]) && acc(&s.HopFields[j])
		//@ fold s.HopFields[i].Mem()
		//@ fold s.HopFields[j].Mem()
		//@ fold s.Mem(ubuf)
	}
	//@ )
	// Update CurrINF and CurrHF and SegLens
	//@ preserves s.Mem(ubuf)
	//@ ensures before(unfolding s.Mem(ubuf) in s.Base.InfValid()) ==> unfolding s.Mem(ubuf) in s.Base.InfValid()
	//@ decreases
	//@ outline(
	//@ unfold s.Mem(ubuf)
	//@ unfold s.Base.Mem()
	s.PathMeta.CurrINF = uint8(s.NumINF) - s.PathMeta.CurrINF - 1
	s.PathMeta.CurrHF = uint8(s.NumHops) - s.PathMeta.CurrHF - 1
	//@ fold s.Base.Mem()
	//@ fold s.Mem(ubuf)
	//@ )
	return s, nil
}

// ToRaw tranforms scion.Decoded into scion.Raw.
// @ preserves s.Mem(ubuf1)
// @ preserves slices.AbsSlice_Bytes(ubuf1, 0, len(ubuf1))
// @ ensures   err == nil ==> r.Mem(ubuf2)
// @ ensures   err != nil ==> err.ErrorMem()
// @ decreases
func (s *Decoded) ToRaw( /*@ ghost ubuf1 []byte @*/ ) (r *Raw, err error /*@, ghost ubuf2 []byte @*/) {
	// (VerifiedSCION) if `tmp` is not used, Gobra complains that
	// make cannot contain ghost subexpressions
	tmp := s.Len( /*@ ubuf1 @*/ )
	b := make([]byte, tmp)
	//@ fold slices.AbsSlice_Bytes(b, 0, len(b))
	if err := s.SerializeTo(b /*@, ubuf1 @*/); err != nil {
		return nil, err /*@, b @*/
	}
	raw := &Raw{}
	//@ fold raw.Base.NonInitMem()
	//@ fold raw.NonInitMem()
	if err := raw.DecodeFromBytes(b); err != nil {
		return nil, err /*@, b @*/
	}
	return raw, nil /*@, b @*/
}
