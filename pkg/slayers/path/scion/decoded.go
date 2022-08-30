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
//@ requires  s.NonInitMem()
//@ preserves acc(slices.AbsSlice_Bytes(data, 0, len(data)), definitions.ReadL1)
//@ ensures   r == nil ==> s.Mem()
//@ ensures   r != nil ==> (r.ErrorMem() && s.NonInitMem())
//@ decreases
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
	//@ ghost slices.SplitByIndex_Bytes(data, 0, len(data), offset, definitions.ReadL1)
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
	for i := 0; i < /*@ unfolding acc(s.Base.Mem(), definitions.ReadL1) in @*/ s.NumINF; i++ {
		// assert acc(&s.InfoFields[i])
		// assert offset + path.InfoLen <= len(data)
		//@ ghost slices.SplitByIndex_Bytes(data, offset, len(data), offset + path.InfoLen, definitions.ReadL1)
		//@ ghost slices.Reslice_Bytes(data, offset, offset + path.InfoLen, definitions.ReadL1)
		if err := s.InfoFields[i].DecodeFromBytes(data[offset : offset+path.InfoLen]); err != nil {
			//@ ghost slices.Unslice_Bytes(data, offset, offset + path.InfoLen, definitions.ReadL1)
			//@ ghost slices.CombineAtIndex_Bytes(data, offset, len(data), offset + path.InfoLen, definitions.ReadL1)
			//@ ghost slices.CombineAtIndex_Bytes(data, 0, len(data), offset, definitions.ReadL1)
			//@ apply s.Base.Mem() --* s.Base.NonInitMem()
			//@ fold s.NonInitMem()
			return err
		}
		//@ assert len(data[offset:offset+path.InfoLen]) == path.InfoLen
		//@ ghost slices.Unslice_Bytes(data, offset, offset + path.InfoLen, definitions.ReadL1)
		//@ ghost slices.CombineAtIndex_Bytes(data, 0, offset + path.InfoLen, offset, definitions.ReadL1)
		offset += path.InfoLen
	}
	s.HopFields = make([]path.HopField, ( /*@ unfolding s.Base.Mem() in @*/ s.NumHops))
	//@ invariant acc(&s.HopFields)
	//@ invariant acc(s.Base.Mem(), definitions.ReadL1)
	//@ invariant len(s.HopFields) == s.Base.getNumHops()
	//@ invariant 0 <= i && i <= s.Base.getNumHops()
	//@ invariant forall j int :: i <= j && j < s.Base.getNumHops() ==>
	//@ 	acc(&s.HopFields[j])
	//@ invariant forall j int :: 0 <= j && j < i ==>
	//@  	s.HopFields[j].Mem()
	//@ invariant len(data) >= MetaLen + s.Base.getNumINF() * path.InfoLen + s.Base.getNumHops() * path.HopLen
	//@ invariant offset == MetaLen + s.Base.getNumINF() * path.InfoLen + i * path.HopLen
	//@ invariant acc(slices.AbsSlice_Bytes(data, 0, offset), definitions.ReadL1)
	//@ invariant acc(slices.AbsSlice_Bytes(data, offset, len(data)), definitions.ReadL1)
	//@ decreases s.Base.getNumHops() - i
	for i := 0; i < /*@ unfolding acc(s.Base.Mem(), definitions.ReadL1) in @*/ s.NumHops; i++ {
		// assert acc(&s.HopFields[i])
		// assert offset + path.HopLen <= len(data)
		//@ ghost slices.SplitByIndex_Bytes(data, offset, len(data), offset + path.HopLen, definitions.ReadL1)
		//@ ghost slices.Reslice_Bytes(data, offset, offset + path.HopLen, definitions.ReadL1)
		if err := s.HopFields[i].DecodeFromBytes(data[offset : offset+path.HopLen]); err != nil {
			//@ ghost slices.Unslice_Bytes(data, offset, offset + path.HopLen, definitions.ReadL1)
			//@ ghost slices.CombineAtIndex_Bytes(data, offset, len(data), offset + path.HopLen, definitions.ReadL1)
			//@ ghost slices.CombineAtIndex_Bytes(data, 0, len(data), offset, definitions.ReadL1)
			//@ apply s.Base.Mem() --* s.Base.NonInitMem()
			//@ fold s.NonInitMem()
			return err
		}
		//@ assert len(data[offset:offset+path.HopLen]) == path.HopLen
		//@ ghost slices.Unslice_Bytes(data, offset, offset + path.HopLen, definitions.ReadL1)
		//@ ghost slices.CombineAtIndex_Bytes(data, 0, offset + path.HopLen, offset, definitions.ReadL1)
		offset += path.HopLen
	}
	//@ ghost slices.CombineAtIndex_Bytes(data, 0, len(data), offset, definitions.ReadL1)
	//@ fold s.Mem()
	return nil
}

// SerializeTo writePerms the path to a slice. The slice must be big enough to hold the entire data,
// otherwise an error is returned.
//@ preserves acc(s.Mem(), definitions.ReadL1)
//@ preserves slices.AbsSlice_Bytes(b, 0, len(b))
//@ ensures   r != nil ==> r.ErrorMem()
//@ decreases
func (s *Decoded) SerializeTo(b []byte) (r error) {
	if len(b) < s.Len() {
		ret := serrors.New("buffer too small to serialize path.", "expected", s.Len(),
			"actual", int(len(b)))
		return ret
	}
	//@ unfold acc(s.Mem(), definitions.ReadL1)
	//@ unfold acc(s.Base.Mem(), definitions.ReadL1)
	//@ ghost slices.SplitByIndex_Bytes(b, 0, len(b), MetaLen, writePerm)
	//@ ghost slices.Reslice_Bytes(b, 0, MetaLen, writePerm)
	if err := s.PathMeta.SerializeTo(b[:MetaLen]); err != nil {
		//@ ghost slices.Unslice_Bytes(b, 0, MetaLen, writePerm)
		//@ ghost slices.CombineAtIndex_Bytes(b, 0, len(b), MetaLen, writePerm)
		//@ fold acc(s.Base.Mem(), definitions.ReadL1)
		//@ fold acc(s.Mem(), definitions.ReadL1)
		return err
	}
	//@ ghost slices.Unslice_Bytes(b, 0, MetaLen, writePerm)
	//@ ghost slices.CombineAtIndex_Bytes(b, 0, len(b), MetaLen, writePerm)
	offset := MetaLen
	//@ assert len(b) >= MetaLen + s.NumINF * path.InfoLen + s.NumHops * path.HopLen
	//@ ghost slices.SplitByIndex_Bytes(b, 0, len(b), offset, writePerm)
	//@ fold acc(s.Base.Mem(), definitions.ReadL1)
	//@ fold acc(s.Mem(), definitions.ReadL1)
	//@ invariant acc(s.Mem(), definitions.ReadL1)
	//@ invariant slices.AbsSlice_Bytes(b, 0, offset)
	//@ invariant slices.AbsSlice_Bytes(b, offset, len(b))
	//@ invariant 0 <= i && i <= s.getLenInfoFields()
	//@ invariant offset == MetaLen + i * path.InfoLen
	//@ invariant len(b) >= MetaLen + s.getLenInfoFields() * path.InfoLen + s.getLenHopFields() * path.HopLen
	//@ decreases s.getLenInfoFields() - i
	// --- TODO reinstate the original range clause
	// for _, info := range s.InfoFields {
	for i := 0; i < /*@ unfolding acc(s.Mem(), definitions.ReadL1) in @*/ len(s.InfoFields); i++ {
		//@ unfold acc(s.Mem(), definitions.ReadL1)
		info := &s.InfoFields[i]
		//@ ghost slices.SplitByIndex_Bytes(b, offset, len(b), offset + path.InfoLen, writePerm)
		//@ ghost slices.Reslice_Bytes(b, offset, offset + path.InfoLen, writePerm)
		if err := info.SerializeTo(b[offset : offset+path.InfoLen]); err != nil {
			//@ ghost slices.Unslice_Bytes(b, offset, offset + path.InfoLen, writePerm)
			//@ ghost slices.CombineAtIndex_Bytes(b, offset, len(b), offset + path.InfoLen, writePerm)
			//@ ghost slices.CombineAtIndex_Bytes(b, 0, len(b), offset, writePerm)
			//@ fold acc(s.Mem(), definitions.ReadL1)
			return err
		}
		//@ fold acc(s.Mem(), definitions.ReadL1)
		//@ assert len(b[offset:offset+path.InfoLen]) == path.InfoLen
		//@ ghost slices.Unslice_Bytes(b, offset, offset + path.InfoLen, writePerm)
		//@ ghost slices.CombineAtIndex_Bytes(b, 0, offset + path.InfoLen, offset, writePerm)
		offset += path.InfoLen
	}
	//@ assert offset == MetaLen + s.getLenInfoFields() * path.InfoLen
	//@ assert len(b) >= MetaLen + s.getLenInfoFields() * path.InfoLen + s.getLenHopFields() * path.HopLen
	//@ invariant acc(s.Mem(), definitions.ReadL1)
	//@ invariant slices.AbsSlice_Bytes(b, 0, offset)
	//@ invariant slices.AbsSlice_Bytes(b, offset, len(b))
	//@ invariant 0 <= i && i <= s.getLenHopFields()
	//@ invariant offset == MetaLen + s.getLenInfoFields() * path.InfoLen + i * path.HopLen
	//@ invariant len(b) >= MetaLen + s.getLenInfoFields() * path.InfoLen + s.getLenHopFields() * path.HopLen
	//@ decreases s.getLenHopFields() - i
	// --- TODO reinstate the original range clause
	// for _, hop := range s.HopFields {
	for i := 0; i < /*@ unfolding acc(s.Mem(), definitions.ReadL1) in @*/ len(s.HopFields); i++ {
		//@ unfold acc(s.Mem(), definitions.ReadL1)
		hop := &s.HopFields[i]
		//@ ghost slices.SplitByIndex_Bytes(b, offset, len(b), offset + path.HopLen, writePerm)
		//@ ghost slices.Reslice_Bytes(b, offset, offset + path.HopLen, writePerm)
		if err := hop.SerializeTo(b[offset : offset+path.HopLen]); err != nil {
			//@ ghost slices.Unslice_Bytes(b, offset, offset + path.HopLen, writePerm)
			//@ ghost slices.CombineAtIndex_Bytes(b, offset, len(b), offset + path.HopLen, writePerm)
			//@ ghost slices.CombineAtIndex_Bytes(b, 0, len(b), offset, writePerm)
			//@ fold acc(s.Mem(), definitions.ReadL1)
			return err
		}
		//@ assert len(b[offset:offset+path.HopLen]) == path.HopLen
		//@ ghost slices.Unslice_Bytes(b, offset, offset + path.HopLen, writePerm)
		//@ ghost slices.CombineAtIndex_Bytes(b, 0, offset + path.HopLen, offset, writePerm)
		//@ fold acc(s.Mem(), definitions.ReadL1)
		offset += path.HopLen
	}
	//@ ghost slices.CombineAtIndex_Bytes(b, 0, len(b), offset, writePerm)
	return nil
}

// Reverse reverses a SCION path.
//@ trusted // depends on the changes from https://github.com/scionproto/scion/issues/4241 to verify
//@ requires s.Mem()
//@ ensures  r == nil ==> p != nil
//@ ensures  r == nil ==> p.Mem()
//@ ensures  r != nil ==> r.ErrorMem() && s.Mem()
//@ decreases
func (s *Decoded) Reverse() (p path.Path, r error) {
	if s.NumINF == 0 {
		return nil, serrors.New("empty decoded path is invalid and cannot be reversed")
	}
	// Reverse order of InfoFields and SegLens
	for i, j := 0, s.NumINF-1; i < j; i, j = i+1, j-1 {
		s.InfoFields[i], s.InfoFields[j] = s.InfoFields[j], s.InfoFields[i]
		s.PathMeta.SegLen[i], s.PathMeta.SegLen[j] = s.PathMeta.SegLen[j], s.PathMeta.SegLen[i]
	}
	// Reverse cons dir flags
	for i := 0; i < s.NumINF; i++ {
		info := &s.InfoFields[i]
		info.ConsDir = !info.ConsDir
	}
	// Reverse order of hop fields
	for i, j := 0, s.NumHops-1; i < j; i, j = i+1, j-1 {
		s.HopFields[i], s.HopFields[j] = s.HopFields[j], s.HopFields[i]
	}
	// Update CurrINF and CurrHF and SegLens
	s.PathMeta.CurrINF = uint8(s.NumINF) - s.PathMeta.CurrINF - 1
	s.PathMeta.CurrHF = uint8(s.NumHops) - s.PathMeta.CurrHF - 1

	return s, nil
}

// ToRaw tranforms scion.Decoded into scion.Raw.
//@ preserves acc(s.Mem(), definitions.ReadL1)
//@ ensures err == nil ==> r.Mem()
//@ decreases
func (s *Decoded) ToRaw() (r *Raw, err error) {
	b := make([]byte, s.Len())
	//@ fold slices.AbsSlice_Bytes(b, 0, len(b))
	if err := s.SerializeTo(b); err != nil {
		return nil, err
	}
	raw := &Raw{}
	//@ fold raw.Base.NonInitMem()
	//@ fold raw.NonInitMem()
	if err := raw.DecodeFromBytes(b); err != nil {
		return nil, err
	}
	return raw, nil
}
