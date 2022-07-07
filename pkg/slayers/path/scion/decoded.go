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
//@ requires s.NonInitMem()
//@ requires len(data) >= MetaLen
//@ preserves forall i int :: 0 <= i && i < len(data) ==>
//@   acc(&data[i], definitions.ReadL1)
//@ ensures r == nil ==> s.Mem()
//@ ensures r != nil ==> s.NonInitMem()
//@ decreases
func (s *Decoded) DecodeFromBytes(data []byte) (r error) {
	//@ unfold s.NonInitMem()
	if err := s.Base.DecodeFromBytes(data); err != nil {
		//@ fold s.NonInitMem()
		return err
	}
	if minLen := s.Len(); len(data) < minLen {
		//@ s.Base.exchangePred()
		//@ fold s.NonInitMem()
		return serrors.New("DecodedPath raw too short", "expected", minLen, "actual", int(len(data)))
	}
	//@ assert s.Base.Mem()
	//@ assert s.Base.getNumINF() >= 0
	//@ assert s.Base.getNumHops() >= 0
	//@ assert len(data) >= MetaLen + s.Base.getNumINF() * path.InfoLen + s.Base.getNumHops() * path.HopLen
	//@ assert acc(&s.InfoFields)
	//@ assert acc(&s.HopFields)
	offset := MetaLen
	// (gavin) changed to use pure func and avoid unfolding
	s.InfoFields = make([]path.InfoField, s.Base.getNumINF() /* s.NumINF */)
	//@ invariant acc(&s.InfoFields)
	//@ invariant acc(s.Base.Mem(), definitions.ReadL1)
	//@ invariant len(s.InfoFields) == s.Base.getNumINF()
	//@ invariant 0 <= i && i <= s.Base.getNumINF()
	//@ invariant len(data) >= MetaLen + s.Base.getNumINF() * path.InfoLen + s.Base.getNumHops() * path.HopLen
	//@ invariant offset == MetaLen + i * path.InfoLen
	//@ invariant forall j int :: 0 <= j && j < s.Base.getNumINF() ==>
	//@ 	acc(&s.InfoFields[j])
	//@ invariant forall j int :: 0 <= j && j < len(data) ==>
	//@   acc(&data[j], definitions.ReadL1)
	//@ decreases s.Base.getNumINF() - i
	// (gavin) changed to use pure func and avoid unfolding
	// for i := 0; i < s.NumINF; i++ {
	for i := 0; i < s.Base.getNumINF(); i++ {
		//@ assert acc(&s.InfoFields[i])
		//@ assert 0 <= offset && offset < len(data)
		//@ assert 0 <= offset+path.InfoLen && offset+path.InfoLen <= len(data)
		//@ assert forall j int :: 0 <= j && j < path.InfoLen ==> &data[offset : offset+path.InfoLen][j] == &data[offset + j]
		if err := s.InfoFields[i].DecodeFromBytes(data[offset : offset+path.InfoLen]); err != nil {
			//@ ghost s.Base.exchangePred()
			//@ fold s.NonInitMem()
			return err
		}
		offset += path.InfoLen
	}
	// (gavin) changed to use pure func and avoid unfolding
	s.HopFields = make([]path.HopField, s.Base.getNumHops() /* s.NumHops */)
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
	//@ invariant forall j int :: 0 <= j && j < len(data) ==>
	//@   acc(&data[j], definitions.ReadL1)
	//@ decreases s.Base.getNumHops() - i
	// (gavin) changed to use pure func and avoid unfolding
	// for i := 0; i < s.NumHops; i++ {
	for i := 0; i < s.Base.getNumHops(); i++ {
		//@ assert acc(&s.HopFields[i])
		//@ assert 0 <= offset && offset < len(data)
		//@ assert 0 <= offset+path.InfoLen && offset+path.HopLen <= len(data)
		//@ assert forall j int :: 0 <= j && j < int(path.HopLen) ==>
		//@   &(data[offset : offset+path.HopLen][j]) == &data[offset + j]
		if err := s.HopFields[i].DecodeFromBytes(data[offset : offset+path.HopLen]); err != nil {
			//@ ghost s.Base.exchangePred()
			//@ fold s.NonInitMem()
			return err
		}
		offset += path.HopLen
	}
	//@ fold s.Mem()
	return nil
}

// SerializeTo writes the path to a slice. The slice must be big enough to hold the entire data,
// otherwise an error is returned.
//@ preserves acc(s.Mem(), definitions.ReadL1)
//@ preserves forall i int :: 0 <= i && i < len(b) ==>
//@   acc(&b[i])
//@ decreases
func (s *Decoded) SerializeTo(b []byte) error {
	//@ unfold acc(s.Mem(), definitions.ReadL1)
	if len(b) < s.Len() {
		//@ assume false // TODO ask Joao / Dion
		ret := serrors.New("buffer too small to serialize path.", "expected", s.Len(),
			"actual", len(b))
		//@ fold acc(s.Mem(), definitions.ReadL1)
		return ret
	}
	//@ unfold acc(s.Base.Mem(), definitions.ReadL1)
	if err := s.PathMeta.SerializeTo(b[:MetaLen]); err != nil {
		//@ fold acc(s.Base.Mem(), definitions.ReadL1)
		//@ fold acc(s.Mem(), definitions.ReadL1)
		return err
	}
	offset := MetaLen
	//@ assert len(b) >= MetaLen + s.NumINF * path.InfoLen + s.NumHops * path.HopLen
	//@ fold acc(s.Base.Mem(), definitions.ReadL1)
	//@ assert path.InfoLen >= 0
	//@ assert path.HopLen >= 0
	//  assert forall i int :: 0 <= i && i < len(b) ==>
	//    acc(&b[i])
	//  assert len(b) >= MetaLen + s.Base.getNumINF() * path.InfoLen + s.Base.getNumHops() * path.HopLen

	//@ fold acc(s.Mem(), definitions.ReadL1)

	//@ assert 0 <= s.getLenInfoFields()
	//@ assert 0 <= s.getLenHopFields()
	//  assert acc(s.Mem(), definitions.ReadL1)
	//  assert len(b) >= MetaLen + s.getLenInfoFields() * path.InfoLen + s.getLenHopFields() * path.HopLen

	//@ invariant acc(s.Mem(), definitions.ReadL1)
	//@ invariant forall i int :: 0 <= i && i < len(b) ==>
	//@   acc(&b[i])
	//@ invariant 0 <= i && i <= s.getLenInfoFields()
	//@ invariant offset == MetaLen + i * path.InfoLen
	//@ invariant len(b) >= MetaLen + s.getLenInfoFields() * path.InfoLen + s.getLenHopFields() * path.HopLen
	//@ decreases s.getLenInfoFields() - i
	// --- TODO reinstate the original range clause
	// for _, info := range s.InfoFields {
	for i := 0; i < s.getLenInfoFields(); i++ {
		//@ unfold acc(s.Mem(), definitions.ReadL1)
		//@ assert acc(&s.InfoFields[i], definitions.ReadL1)
		//@ assert len(b) >= offset + path.InfoLen
		//@ assert offset >= 0 && offset + path.InfoLen >= 0
		//@ assert offset < offset+path.InfoLen
		info := &s.InfoFields[i]
		//@ assert len(b[offset : offset + path.InfoLen]) == path.InfoLen
		//@ assert forall j int :: 0 <= j && j < len(b[offset : offset + path.InfoLen]) ==>
		//@   &b[offset : offset + path.InfoLen][j] == &b[offset + j]
		if err := info.SerializeTo(b[offset : offset+path.InfoLen]); err != nil {
			//@ fold acc(s.Mem(), definitions.ReadL1)
			return err
		}
		//@ fold acc(s.Mem(), definitions.ReadL1)
		offset += path.InfoLen
	}

	//@ assert offset == MetaLen + s.getLenInfoFields() * path.InfoLen
	//@ assert len(b) >= MetaLen + s.getLenInfoFields() * path.InfoLen + s.getLenHopFields() * path.HopLen

	//@ invariant acc(s.Mem(), definitions.ReadL1)
	//@ invariant forall i int :: 0 <= i && i < len(b) ==>
	//@   acc(&b[i])
	//@ invariant 0 <= i && i <= s.getLenHopFields()
	//@ invariant offset == MetaLen + s.getLenInfoFields() * path.InfoLen + i * path.HopLen
	//@ invariant len(b) >= MetaLen + s.getLenInfoFields() * path.InfoLen + s.getLenHopFields() * path.HopLen
	//@ decreases s.getLenHopFields() - i
	// --- TODO reinstate the original range clause
	// for _, hop := range s.HopFields {
	for i := 0; i < s.getLenHopFields(); i++ {
		//@ unfold acc(s.Mem(), definitions.ReadL1)
		//@ assert acc(s.HopFields[i].Mem(), definitions.ReadL1)
		//@ assert len(b) >= offset + path.HopLen
		//@ assert offset >= 0 && offset + path.HopLen >= 0
		//@ assert offset < offset + path.HopLen
		hop := &s.HopFields[i]
		//@ assert len(b[offset : offset + path.HopLen]) == path.HopLen
		//@ assert forall j int :: 0 <= j && j < len(b[offset : offset + path.HopLen]) ==>
		//@   &b[offset : offset + path.HopLen][j] == &b[offset + j]
		if err := hop.SerializeTo(b[offset : offset+path.HopLen]); err != nil {
			//@ fold acc(s.Mem(), definitions.ReadL1)
			return err
		}
		//@ fold acc(s.Mem(), definitions.ReadL1)
		offset += path.HopLen
	}
	return nil
}

// Reverse reverses a SCION path.
//
// TODO this method suffers from the
// same issue with embedded interfaces as:
// https://github.com/viperproject/gobra/issues/461
//
//@ trusted
//@ requires s.Mem()
//@ ensures r != nil ==> s.Mem()
//@ ensures r == nil ==> p.Mem()
//@ decreases
func (s *Decoded) Reverse() (p path.Path, r error) {
	if s.NumINF == 0 {
		// Empty path doesn't need reversal.
		return nil, nil
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
func (s *Decoded) ToRaw() (r *Raw, err error) {
	//@ unfold acc(s.Mem(), definitions.ReadL1)
	b := make([]byte, s.Len())
	//@ fold acc(s.Mem(), definitions.ReadL1)
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
