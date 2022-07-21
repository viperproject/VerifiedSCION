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

// Raw is a raw representation of the SCION (data-plane) path type. It is designed to parse as
// little as possible and should be used if performance matters.
type Raw struct {
	Base
	Raw []byte
}

// DecodeFromBytes only decodes the PathMetaHeader. Otherwise the nothing is decoded and simply kept
// as raw bytes.
//@ requires s.NonInitMem()
//@ requires len(data) >= MetaLen
//@ requires forall i int :: 0 <= i && i < len(data) ==>
//@   acc(&data[i])
//@ ensures res == nil ==> s.Mem()
//@ ensures res != nil ==> (s.NonInitMem() && res.ErrorMem())
//@ decreases
func (s *Raw) DecodeFromBytes(data []byte) (res error) {
	//@ unfold s.NonInitMem()
	if err := s.Base.DecodeFromBytes(data); err != nil {
		//@ fold s.NonInitMem()
		return err
	}
	pathLen := s.Len()
	if len(data) < pathLen {
		//@ s.Base.exchangePred()
		//@ fold s.NonInitMem()
		return serrors.New("RawPath raw too short", "expected", pathLen, "actual", int(len(data)))
	}
	//@ assert s.Base.Mem()
	//@ assert 0 <= pathLen
	//@ assert len(data) >= pathLen
	//@ assert forall i int :: 0 <= i && i < pathLen ==>
	//@   (&data[:pathLen][i] == &data[i] && acc(&data[i]))
	s.Raw = data[:pathLen]
	//@ fold s.Mem()
	return nil
}

// SerializeTo writes the path to a slice. The slice must be big enough to hold the entire data,
// otherwise an error is returned.
//@ requires s.Mem()
// requires len(b) >= unfolding s.Mem() in s.Base.Len()
//@ preserves forall i int :: 0 <= i && i < len(b) ==>
//@   acc(&b[i])
//@ ensures s.Mem()
//@ decreases
func (s *Raw) SerializeTo(b []byte) error {
	//@ assert MetaLen == 4
	//@ unfold s.Mem()
	if s.Raw == nil {
		//@ fold s.Mem()
		return serrors.New("raw is nil")
	}
	if minLen := s.Len(); len(b) < minLen {
		//@ fold s.Mem()
		return serrors.New("buffer too small", "expected", minLen, "actual", int(len(b)))
	}
	// XXX(roosd): This modifies the underlying buffer. Consider writing to data
	// directly.
	//@ unfold s.Base.Mem()
	//
	// (gavin) unroll quantifiers
	// assert forall i int :: 0 <= i && i < MetaLen ==>
	//   &s.Raw[i] == &s.Raw[:MetaLen][i]
	//@ assert &s.Raw[0] == &s.Raw[:MetaLen][0]
	//@ assert &s.Raw[1] == &s.Raw[:MetaLen][1]
	//@ assert &s.Raw[2] == &s.Raw[:MetaLen][2]
	//@ assert &s.Raw[3] == &s.Raw[:MetaLen][3]
	if err := s.PathMeta.SerializeTo(s.Raw[:MetaLen]); err != nil {
		//@ fold s.Base.Mem()
		//@ fold s.Mem()
		return err
	}
	copy(b, s.Raw /*@ , definitions.ReadL1 @*/)
	//@ fold s.Base.Mem()
	//@ fold s.Mem()
	return nil
}

// Reverse reverses the path such that it can be used in the reverse direction.
//
// TODO this method suffers from the
// same issue with embedded interfaces as:
// https://github.com/viperproject/gobra/issues/461
//
//@ trusted
//@ requires s.Mem()
//@ ensures err == nil ==> p.Mem()
//@ ensures err != nil ==> s.Mem()
//@ decreases
func (s *Raw) Reverse() (p path.Path, err error) {
	// XXX(shitz): The current implementation is not the most performant, since it parses the entire
	// path first. If this becomes a performance bottleneck, the implementation should be changed to
	// work directly on the raw representation.

	decoded, err := s.ToDecoded()
	if err != nil {
		return nil, err
	}
	reversed, err := decoded.Reverse()
	if err != nil {
		return nil, err
	}
	if err := reversed.SerializeTo(s.Raw); err != nil {
		return nil, err
	}
	err = s.DecodeFromBytes(s.Raw)
	return s, err
}

// ToDecoded transforms a scion.Raw to a scion.Decoded.
//@ requires s.Mem()
//@ requires unfolding s.Mem() in len(s.Raw) >= MetaLen
//@ ensures s.Mem()
//@ ensures err == nil ==> d.Mem()
//@ decreases
func (s *Raw) ToDecoded() (d *Decoded, err error) {
	//@ unfold s.Mem()
	//@ unfold s.Base.Mem()
	// (gavin) unroll quantifiers
	// assert forall i int :: 0 <= i && i < MetaLen ==>
	//   &s.Raw[:MetaLen][i] == &s.Raw[i]
	//@ assert MetaLen == 4
	//@ assert &s.Raw[:MetaLen][0] == &s.Raw[0]
	//@ assert &s.Raw[:MetaLen][1] == &s.Raw[1]
	//@ assert &s.Raw[:MetaLen][2] == &s.Raw[2]
	//@ assert &s.Raw[:MetaLen][3] == &s.Raw[3]
	//@ assert len(s.Raw[:MetaLen]) >= MetaLen
	// Serialize PathMeta to ensure potential changes are reflected Raw.
	if err := s.PathMeta.SerializeTo(s.Raw[:MetaLen]); err != nil {
		//@ fold s.Base.Mem()
		//@ fold s.Mem()
		return nil, err
	}
	//@ fold s.Base.Mem()
	decoded := &Decoded{}
	//@ fold decoded.Base.NonInitMem()
	//@ fold decoded.NonInitMem()
	if err := decoded.DecodeFromBytes(s.Raw); err != nil {
		//@ fold s.Mem()
		return nil, err
	}
	//@ fold s.Mem()
	return decoded, nil
}

// IncPath increments the path and writes it to the buffer.
//@ requires s.Mem()
//@ requires unfolding s.Mem() in
//@   unfolding s.Base.Mem() in
//@     (s.NumINF > 0 && int(s.PathMeta.CurrHF) < s.NumHops-1)
//@ ensures s.Mem()
//@ decreases
func (s *Raw) IncPath() error {
	//@ unfold s.Mem()
	if err := s.Base.IncPath(); err != nil {
		//@ fold s.Mem()
		return err
	}
	//@ unfold s.Base.Mem()
	err := s.PathMeta.SerializeTo(s.Raw[:MetaLen])
	//@ fold s.Base.Mem()
	//@ fold s.Mem()
	return err
}

// GetInfoField returns the InfoField at a given index.
//@ requires acc(s.Mem(), definitions.ReadL1)
//@ requires 0 <= idx
//@ ensures  acc(s.Mem(), definitions.ReadL1)
//@ decreases
func (s *Raw) GetInfoField(idx int) (ifield path.InfoField, err error) {
	//@ assert path.InfoLen == 8
	//@ unfold acc(s.Mem(), definitions.ReadL1)
	//@ unfold acc(s.Base.Mem(), definitions.ReadL1)
	// (gavin) changed to pure method to avoid unfolding
	if idx >= s.NumINF {
		e := serrors.New("InfoField index out of bounds", "max", s.NumINF-1, "actual", idx)
		//@ fold acc(s.Base.Mem(), definitions.ReadL1)
		//@ fold acc(s.Mem(), definitions.ReadL1)
		return path.InfoField{}, e
	}
	//@ fold acc(s.Base.Mem(), definitions.ReadL1)
	infOffset := MetaLen + idx*path.InfoLen
	// (gavin) added '&', see: https://github.com/viperproject/gobra/issues/475
	info := &path.InfoField{}
	// (gavin) unroll quantifiers
	// assert forall i int :: 0 <= i && i < path.InfoLen ==>
	//   &s.Raw[infOffset : infOffset+path.InfoLen][i] == &s.Raw[infOffset + i]
	//@ assert &s.Raw[infOffset : infOffset+path.InfoLen][0] == &s.Raw[infOffset + 0]
	//@ assert &s.Raw[infOffset : infOffset+path.InfoLen][1] == &s.Raw[infOffset + 1]
	//@ assert &s.Raw[infOffset : infOffset+path.InfoLen][2] == &s.Raw[infOffset + 2]
	//@ assert &s.Raw[infOffset : infOffset+path.InfoLen][3] == &s.Raw[infOffset + 3]
	//@ assert &s.Raw[infOffset : infOffset+path.InfoLen][4] == &s.Raw[infOffset + 4]
	//@ assert &s.Raw[infOffset : infOffset+path.InfoLen][5] == &s.Raw[infOffset + 5]
	//@ assert &s.Raw[infOffset : infOffset+path.InfoLen][6] == &s.Raw[infOffset + 6]
	//@ assert &s.Raw[infOffset : infOffset+path.InfoLen][7] == &s.Raw[infOffset + 7]
	//@ assert len(s.Raw[infOffset : infOffset+path.InfoLen]) >= path.InfoLen
	if err := info.DecodeFromBytes(s.Raw[infOffset : infOffset+path.InfoLen]); err != nil {
		//@ fold acc(s.Mem(), definitions.ReadL1)
		return path.InfoField{}, err
	}
	//@ fold acc(s.Mem(), definitions.ReadL1)
	// (gavin) added '*' to complement reference addition
	return *info, nil
}

// GetCurrentInfoField is a convenience method that returns the current hop field pointed to by the
// CurrINF index in the path meta header.
//@ preserves acc(s.Mem(), definitions.ReadL1)
//@ decreases
func (s *Raw) GetCurrentInfoField() (path.InfoField, error) {
	//@ unfold acc(s.Mem(), definitions.ReadL1)
	//@ unfold acc(s.Base.Mem(), definitions.ReadL1)
	// (gavin) introduced idx variable
	idx := int(s.PathMeta.CurrINF)
	// (gavin) CurrINF is a uint and must be positive
	//@ assume 0 <= idx
	//@ fold acc(s.Base.Mem(), definitions.ReadL1)
	//@ fold acc(s.Mem(), definitions.ReadL1)
	return s.GetInfoField(idx)
}

// SetInfoField updates the InfoField at a given index.
//@ requires  0 <= idx
//@ preserves s.Mem()
//@ decreases
func (s *Raw) SetInfoField(info path.InfoField, idx int) error {
	//@ share info
	infoRef := &info
	//@ assert path.InfoLen == 8
	//@ unfold s.Mem()
	//@ unfold s.Base.Mem()
	if idx >= s.NumINF {
		err := serrors.New("InfoField index out of bounds", "max", s.NumINF-1, "actual", idx)
		//@ fold s.Base.Mem()
		//@ fold s.Mem()
		return err
	}
	infOffset := MetaLen + idx*path.InfoLen
	// (gavin) unroll quantifiers
	// assert forall i int :: 0 <= i && i < path.InfoLen ==>
	//   &s.Raw[infOffset : infOffset+path.InfoLen][i] == &s.Raw[infOffset + i]
	//@ assert &s.Raw[infOffset : infOffset+path.InfoLen][0] == &s.Raw[infOffset + 0]
	//@ assert &s.Raw[infOffset : infOffset+path.InfoLen][1] == &s.Raw[infOffset + 1]
	//@ assert &s.Raw[infOffset : infOffset+path.InfoLen][2] == &s.Raw[infOffset + 2]
	//@ assert &s.Raw[infOffset : infOffset+path.InfoLen][3] == &s.Raw[infOffset + 3]
	//@ assert &s.Raw[infOffset : infOffset+path.InfoLen][4] == &s.Raw[infOffset + 4]
	//@ assert &s.Raw[infOffset : infOffset+path.InfoLen][5] == &s.Raw[infOffset + 5]
	//@ assert &s.Raw[infOffset : infOffset+path.InfoLen][6] == &s.Raw[infOffset + 6]
	//@ assert &s.Raw[infOffset : infOffset+path.InfoLen][7] == &s.Raw[infOffset + 7]
	//@ assert len(s.Raw[infOffset : infOffset+path.InfoLen]) >= path.InfoLen
	ret := infoRef.SerializeTo(s.Raw[infOffset : infOffset+path.InfoLen])
	//@ fold s.Base.Mem()
	//@ fold s.Mem()
	return ret
}

// GetHopField returns the HopField at a given index.
//@ requires 0 <= idx
//@ preserves acc(s.Mem(), definitions.ReadL1)
//@ decreases
func (s *Raw) GetHopField(idx int) (path.HopField, error) {
	//@ assert path.HopLen == 12
	//@ unfold acc(s.Mem(), definitions.ReadL1)
	//@ unfold acc(s.Base.Mem(), definitions.ReadL1)
	if idx >= s.NumHops {
		err := serrors.New("HopField index out of bounds", "max", s.NumHops-1, "actual", idx)
		//@ fold acc(s.Base.Mem(), definitions.ReadL1)
		//@ fold acc(s.Mem(), definitions.ReadL1)
		return path.HopField{}, err
	}
	hopOffset := MetaLen + s.NumINF*path.InfoLen + idx*path.HopLen
	//@ fold acc(s.Base.Mem(), definitions.ReadL1)
	// (gavin) added '&'
	hop := &path.HopField{}
	// (gavin) unroll quantifiers
	// assert forall i int :: 0 <= i && i < path.HopLen ==>
	//   &s.Raw[hopOffset:hopOffset+path.HopLen][i] == &s.Raw[hopOffset + i]
	//@ assert path.HopLen == 12
	//@ assert &s.Raw[hopOffset:hopOffset+path.HopLen][0] == &s.Raw[hopOffset +  0]
	//@ assert &s.Raw[hopOffset:hopOffset+path.HopLen][1] == &s.Raw[hopOffset +  1]
	//@ assert &s.Raw[hopOffset:hopOffset+path.HopLen][2] == &s.Raw[hopOffset +  2]
	//@ assert &s.Raw[hopOffset:hopOffset+path.HopLen][3] == &s.Raw[hopOffset +  3]
	//@ assert &s.Raw[hopOffset:hopOffset+path.HopLen][4] == &s.Raw[hopOffset +  4]
	//@ assert &s.Raw[hopOffset:hopOffset+path.HopLen][5] == &s.Raw[hopOffset +  5]
	//@ assert &s.Raw[hopOffset:hopOffset+path.HopLen][6] == &s.Raw[hopOffset +  6]
	//@ assert &s.Raw[hopOffset:hopOffset+path.HopLen][7] == &s.Raw[hopOffset +  7]
	//@ assert &s.Raw[hopOffset:hopOffset+path.HopLen][8] == &s.Raw[hopOffset +  8]
	//@ assert &s.Raw[hopOffset:hopOffset+path.HopLen][9] == &s.Raw[hopOffset +  9]
	//@ assert &s.Raw[hopOffset:hopOffset+path.HopLen][10] == &s.Raw[hopOffset + 10]
	//@ assert &s.Raw[hopOffset:hopOffset+path.HopLen][11] == &s.Raw[hopOffset + 11]
	//@ assert len(s.Raw[hopOffset : hopOffset+path.HopLen]) >= path.HopLen
	if err := hop.DecodeFromBytes(s.Raw[hopOffset : hopOffset+path.HopLen]); err != nil {
		//@ fold acc(s.Mem(), definitions.ReadL1)
		return path.HopField{}, err
	}
	//@ fold acc(s.Mem(), definitions.ReadL1)
	//@ unfold hop.Mem()
	return *hop, nil
}

// GetCurrentHopField is a convenience method that returns the current hop field pointed to by the
// CurrHF index in the path meta header.
//@ preserves acc(s.Mem(), definitions.ReadL1)
//@ decreases
func (s *Raw) GetCurrentHopField() (path.HopField, error) {
	//@ unfold acc(s.Mem(), definitions.ReadL1)
	//@ unfold acc(s.Base.Mem(), definitions.ReadL1)
	idx := int(s.PathMeta.CurrHF)
	// NOTE CurrHF is guaranteed to be positive.
	//@ assume 0 <= idx
	//@ fold acc(s.Base.Mem(), definitions.ReadL1)
	//@ fold acc(s.Mem(), definitions.ReadL1)
	return s.GetHopField(idx)
}

// SetHopField updates the HopField at a given index.
//@ requires 0 <= idx
//@  preserves s.Mem()
//@ decreases
func (s *Raw) SetHopField(hop path.HopField, idx int) error {
	//@ share hop
	hopRef := &hop // (gavin) introduced `hopRef`
	//@ assert path.HopLen == 12
	//@ fold hopRef.Mem()
	//@ unfold s.Mem()
	//@ unfold s.Base.Mem()
	if idx >= s.NumHops {
		// (gavin) introduced `err`
		err := serrors.New("HopField index out of bounds", "max", s.NumHops-1, "actual", idx)
		//@ fold s.Base.Mem()
		//@ fold s.Mem()
		return err
	}
	hopOffset := MetaLen + s.NumINF*path.InfoLen + idx*path.HopLen
	//@ fold s.Base.Mem()
	// (gavin) introduced `ret`
	// (gavin) unroll quantifiers
	// assert forall i int :: 0 <= i && i < path.HopLen ==>
	//   &s.Raw[hopOffset:hopOffset+path.HopLen][i] == &s.Raw[hopOffset + i]
	//@ assert &s.Raw[hopOffset:hopOffset+path.HopLen][0] == &s.Raw[hopOffset +  0]
	//@ assert &s.Raw[hopOffset:hopOffset+path.HopLen][1] == &s.Raw[hopOffset +  1]
	//@ assert &s.Raw[hopOffset:hopOffset+path.HopLen][2] == &s.Raw[hopOffset +  2]
	//@ assert &s.Raw[hopOffset:hopOffset+path.HopLen][3] == &s.Raw[hopOffset +  3]
	//@ assert &s.Raw[hopOffset:hopOffset+path.HopLen][4] == &s.Raw[hopOffset +  4]
	//@ assert &s.Raw[hopOffset:hopOffset+path.HopLen][5] == &s.Raw[hopOffset +  5]
	//@ assert &s.Raw[hopOffset:hopOffset+path.HopLen][6] == &s.Raw[hopOffset +  6]
	//@ assert &s.Raw[hopOffset:hopOffset+path.HopLen][7] == &s.Raw[hopOffset +  7]
	//@ assert &s.Raw[hopOffset:hopOffset+path.HopLen][8] == &s.Raw[hopOffset +  8]
	//@ assert &s.Raw[hopOffset:hopOffset+path.HopLen][9] == &s.Raw[hopOffset +  9]
	//@ assert &s.Raw[hopOffset:hopOffset+path.HopLen][10] == &s.Raw[hopOffset + 10]
	//@ assert &s.Raw[hopOffset:hopOffset+path.HopLen][11] == &s.Raw[hopOffset + 11]
	//@ assert len(s.Raw[hopOffset : hopOffset+path.HopLen]) >= path.HopLen
	ret := hopRef.SerializeTo(s.Raw[hopOffset : hopOffset+path.HopLen])
	//@ fold s.Mem()
	return ret
}

// IsPenultimateHop returns whether the current hop is the penultimate hop on the path.
//@ preserves acc(s.Mem(), definitions.ReadL1)
//@ decreases
func (s *Raw) IsPenultimateHop() bool {
	//@ unfold acc(s.Mem(), definitions.ReadL1)
	//@ unfold acc(s.Base.Mem(), definitions.ReadL1)
	numberHops := s.NumHops
	currentHop := int(s.PathMeta.CurrHF)
	//@ fold acc(s.Base.Mem(), definitions.ReadL1)
	//@ fold acc(s.Mem(), definitions.ReadL1)
	return currentHop == numberHops-2
}

// IsLastHop returns whether the current hop is the last hop on the path.
//@ preserves acc(s.Mem(), definitions.ReadL1)
//@ decreases
func (s *Raw) IsLastHop() bool {
	//@ unfold acc(s.Mem(), definitions.ReadL1)
	//@ unfold acc(s.Base.Mem(), definitions.ReadL1)
	numberHops := s.NumHops
	currentHop := int(s.PathMeta.CurrHF)
	//@ fold acc(s.Base.Mem(), definitions.ReadL1)
	//@ fold acc(s.Mem(), definitions.ReadL1)
	return currentHop == numberHops-1
}
