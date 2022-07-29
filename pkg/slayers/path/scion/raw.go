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
//@ requires slices.AbsSlice_Bytes(data, 0, len(data))
//@ ensures  res == nil ==> s.Mem()
//@ ensures  res != nil ==> (s.NonInitMem() && res.ErrorMem())
//@ decreases
func (s *Raw) DecodeFromBytes(data []byte) (res error) {
	//@ unfold s.NonInitMem()
	if err := s.Base.DecodeFromBytes(data); err != nil {
		//@ fold s.NonInitMem()
		return err
	}
	pathLen := s.Len()
	if len(data) < pathLen {
		//@ apply s.Base.Mem() --* s.Base.NonInitMem()
		//@ fold s.NonInitMem()
		return serrors.New("RawPath raw too short", "expected", pathLen, "actual", int(len(data)))
	}
	// requires s.Base.Mem()
	// requires  s.Len() == pathLen
	// requires  len(data) >= pathLen
	// requires  slices.AbsSlice_Bytes(data, 0, len(data))
	// preserves acc(&s.Raw)
	// ensures   s.Base.Mem()
	// ensures   len(s.Raw) == s.Len()
	// ensures   slices.AbsSlice_Bytes(s.Raw, 0, len(s.Raw))
	// decreases
	// outline (
	//@ ghost slices.SplitByIndex_Bytes(data, 0, len(data), pathLen, writePerm)
	//@ ghost slices.Reslice_Bytes(data, 0, pathLen, writePerm)
	//@ unfold slices.AbsSlice_Bytes(data[:pathLen], 0, len(data[:pathLen]))
	s.Raw = data[:pathLen]
	//@ fold slices.AbsSlice_Bytes(s.Raw, 0, len(s.Raw))
	// )
	//@ fold s.Mem()
	return nil
}

// SerializeTo writePerms the path to a slice. The slice must be big enough to hold the entire data,
// otherwise an error is returned.
//@ requires  s.Mem()
//@ requires  len(b) >= unfolding s.Mem() in s.Len()
//@ preserves slices.AbsSlice_Bytes(b, 0, len(b))
//@ ensures   s.Mem()
//@ ensures   r != nil ==> r.ErrorMem()
//@ decreases
func (s *Raw) SerializeTo(b []byte) (r error) {
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
	//@ ghost slices.SplitByIndex_Bytes(s.Raw, 0, len(s.Raw), MetaLen, writePerm)
	//@ ghost slices.Reslice_Bytes(s.Raw, 0, MetaLen, writePerm)
	if err := s.PathMeta.SerializeTo(s.Raw[:MetaLen]); err != nil {
		//@ ghost slices.Unslice_Bytes(s.Raw, 0, MetaLen, writePerm)
		//@ ghost slices.CombineAtIndex_Bytes(s.Raw, 0, len(b), MetaLen, writePerm)
		//@ fold s.Base.Mem()
		//@ fold s.Mem()
		return err
	}
	//@ ghost slices.Unslice_Bytes(s.Raw, 0, MetaLen, writePerm)
	//@ ghost slices.CombineAtIndex_Bytes(s.Raw, 0, len(s.Raw), MetaLen, writePerm)
	//@ preserves acc(&s.Raw)
	//@ preserves slices.AbsSlice_Bytes(s.Raw, 0, len(s.Raw))
	//@ preserves slices.AbsSlice_Bytes(b, 0, len(b))
	//@ ensures len(s.Raw) == before(len(s.Raw))
	//@ decreases
	//@ outline(
	//@ unfold slices.AbsSlice_Bytes(b, 0, len(b))
	//@ unfold acc(slices.AbsSlice_Bytes(s.Raw, 0, len(s.Raw)), definitions.ReadL1)
	copy(b, s.Raw /*@ , definitions.ReadL1 @*/)
	//@ fold acc(slices.AbsSlice_Bytes(s.Raw, 0, len(s.Raw)), definitions.ReadL1)
	//@ fold slices.AbsSlice_Bytes(b, 0, len(b))
	//@ )
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
//@ ensures  err == nil ==> p.Mem()
//@ ensures  err != nil ==> err.ErrorMem() && s.Mem()
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
//@ ensures  s.Mem()
//@ ensures  err == nil ==> d.Mem()
//@ ensures  err != nil ==> err.ErrorMem()
//@ decreases
func (s *Raw) ToDecoded() (d *Decoded, err error) {
	//@ unfold s.Mem()
	//@ unfold s.Base.Mem()
	// Serialize PathMeta to ensure potential changes are reflected Raw.
	//@ ghost slices.SplitByIndex_Bytes(s.Raw, 0, len(s.Raw), MetaLen, writePerm)
	//@ ghost slices.Reslice_Bytes(s.Raw, 0, MetaLen, writePerm)
	if err := s.PathMeta.SerializeTo(s.Raw[:MetaLen]); err != nil {
		//@ ghost slices.Unslice_Bytes(s.Raw, 0, MetaLen, writePerm)
		//@ ghost slices.CombineAtIndex_Bytes(s.Raw, 0, len(s.Raw), MetaLen, writePerm)
		//@ fold s.Base.Mem()
		//@ fold s.Mem()
		return nil, err
	}
	//@ ghost slices.Unslice_Bytes(s.Raw, 0, MetaLen, writePerm)
	//@ ghost slices.CombineAtIndex_Bytes(s.Raw, 0, len(s.Raw), MetaLen, writePerm)
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

// IncPath increments the path and writePerms it to the buffer.
//@ requires s.Mem()
//@ requires unfolding s.Mem() in unfolding
//@   s.Base.Mem() in
//@     (s.NumINF > 0 && int(s.PathMeta.CurrHF) < s.NumHops-1)
//@ ensures  s.Mem()
//@ ensures  r != nil ==> r.ErrorMem()
//@ decreases
func (s *Raw) IncPath() (r error) {
	//@ unfold s.Mem()
	if err := s.Base.IncPath(); err != nil {
		//@ fold s.Mem()
		return err
	}
	//@ unfold s.Base.Mem()
	//@ ghost slices.SplitByIndex_Bytes(s.Raw, 0, len(s.Raw), MetaLen, writePerm)
	//@ ghost slices.Reslice_Bytes(s.Raw, 0, MetaLen, writePerm)
	err := s.PathMeta.SerializeTo(s.Raw[:MetaLen])
	//@ ghost slices.Unslice_Bytes(s.Raw, 0, MetaLen, writePerm)
	//@ ghost slices.CombineAtIndex_Bytes(s.Raw, 0, len(s.Raw), MetaLen, writePerm)
	//@ fold s.Base.Mem()
	//@ fold s.Mem()
	return err
}

// GetInfoField returns the InfoField at a given index.
//@ requires acc(s.Mem(), definitions.ReadL1)
//@ requires 0 <= idx
//@ ensures  acc(s.Mem(), definitions.ReadL1)
//@ ensures  err != nil ==> err.ErrorMem()
//@ decreases
func (s *Raw) GetInfoField(idx int) (ifield path.InfoField, err error) {
	//@ assert path.InfoLen == 8
	//@ unfold acc(s.Mem(), definitions.ReadL1)
	//@ unfold acc(s.Base.Mem(), definitions.ReadL1)
	if idx >= s.NumINF {
		e := serrors.New("InfoField index out of bounds", "max", s.NumINF-1, "actual", idx)
		//@ fold acc(s.Base.Mem(), definitions.ReadL1)
		//@ fold acc(s.Mem(), definitions.ReadL1)
		return path.InfoField{}, e
	}
	//@ fold acc(s.Base.Mem(), definitions.ReadL1)
	infOffset := MetaLen + idx*path.InfoLen
	info /*@@@*/ := path.InfoField{}
	//@ ghost slices.SplitByIndex_Bytes(s.Raw, 0, len(s.Raw), infOffset, definitions.ReadL1)
	//@ ghost slices.SplitByIndex_Bytes(s.Raw, infOffset, len(s.Raw), infOffset+path.InfoLen, definitions.ReadL1)
	//@ ghost slices.Reslice_Bytes(s.Raw, infOffset, infOffset+path.InfoLen, definitions.ReadL1)
	if err := info.DecodeFromBytes(s.Raw[infOffset : infOffset+path.InfoLen]); err != nil {
		//@ ghost slices.Unslice_Bytes(s.Raw, infOffset, infOffset+path.InfoLen, definitions.ReadL1)
		//@ ghost slices.CombineAtIndex_Bytes(s.Raw, infOffset, len(s.Raw), infOffset+path.InfoLen, definitions.ReadL1)
		//@ ghost slices.CombineAtIndex_Bytes(s.Raw, 0, len(s.Raw), infOffset, definitions.ReadL1)
		//@ fold acc(s.Mem(), definitions.ReadL1)
		return path.InfoField{}, err
	}
	//@ ghost slices.Unslice_Bytes(s.Raw, infOffset, infOffset+path.InfoLen, definitions.ReadL1)
	//@ ghost slices.CombineAtIndex_Bytes(s.Raw, infOffset, len(s.Raw), infOffset+path.InfoLen, definitions.ReadL1)
	//@ ghost slices.CombineAtIndex_Bytes(s.Raw, 0, len(s.Raw), infOffset, definitions.ReadL1)
	//@ fold acc(s.Mem(), definitions.ReadL1)
	return info, nil
}

// GetCurrentInfoField is a convenience method that returns the current hop field pointed to by the
// CurrINF index in the path meta header.
//@ preserves acc(s.Mem(), definitions.ReadL1)
//@ ensures r != nil ==> r.ErrorMem()
//@ decreases
func (s *Raw) GetCurrentInfoField() (res path.InfoField, r error) {
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
//@ ensures   r != nil ==> r.ErrorMem()
//@ decreases
func (s *Raw) SetInfoField(info path.InfoField, idx int) (r error) {
	//@ share info
	//@ unfold s.Mem()
	//@ unfold s.Base.Mem()
	if idx >= s.NumINF {
		err := serrors.New("InfoField index out of bounds", "max", s.NumINF-1, "actual", idx)
		//@ fold s.Base.Mem()
		//@ fold s.Mem()
		return err
	}
	infOffset := MetaLen + idx*path.InfoLen
	//@ ghost slices.SplitByIndex_Bytes(s.Raw, 0, len(s.Raw), infOffset, writePerm)
	//@ ghost slices.SplitByIndex_Bytes(s.Raw, infOffset, len(s.Raw), infOffset+path.InfoLen, writePerm)
	//@ ghost slices.Reslice_Bytes(s.Raw, infOffset, infOffset+path.InfoLen, writePerm)
	ret := info.SerializeTo(s.Raw[infOffset : infOffset+path.InfoLen])
	//@ ghost slices.Unslice_Bytes(s.Raw, infOffset, infOffset+path.InfoLen, writePerm)
	//@ ghost slices.CombineAtIndex_Bytes(s.Raw, infOffset, len(s.Raw), infOffset+path.InfoLen, writePerm)
	//@ ghost slices.CombineAtIndex_Bytes(s.Raw, 0, len(s.Raw), infOffset, writePerm)
	//@ fold s.Base.Mem()
	//@ fold s.Mem()
	return ret
}

// GetHopField returns the HopField at a given index.
//@ requires  0 <= idx
//@ preserves acc(s.Mem(), definitions.ReadL1)
//@ ensures   r != nil ==> r.ErrorMem()
//@ decreases
func (s *Raw) GetHopField(idx int) (res path.HopField, r error) {
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
	hop /*@@@*/ := path.HopField{}
	//@ ghost slices.SplitByIndex_Bytes(s.Raw, 0, len(s.Raw), hopOffset, definitions.ReadL1)
	//@ ghost slices.SplitByIndex_Bytes(s.Raw, hopOffset, len(s.Raw), hopOffset+path.HopLen, definitions.ReadL1)
	//@ ghost slices.Reslice_Bytes(s.Raw, hopOffset, hopOffset+path.HopLen, definitions.ReadL1)
	if err := hop.DecodeFromBytes(s.Raw[hopOffset : hopOffset+path.HopLen]); err != nil {
		//@ ghost slices.Unslice_Bytes(s.Raw, hopOffset, hopOffset+path.HopLen, definitions.ReadL1)
		//@ ghost slices.CombineAtIndex_Bytes(s.Raw, hopOffset, len(s.Raw), hopOffset+path.HopLen, definitions.ReadL1)
		//@ ghost slices.CombineAtIndex_Bytes(s.Raw, 0, len(s.Raw), hopOffset, definitions.ReadL1)
		//@ fold acc(s.Mem(), definitions.ReadL1)
		return path.HopField{}, err
	}
	//@ ghost slices.Unslice_Bytes(s.Raw, hopOffset, hopOffset+path.HopLen, definitions.ReadL1)
	//@ ghost slices.CombineAtIndex_Bytes(s.Raw, hopOffset, len(s.Raw), hopOffset+path.HopLen, definitions.ReadL1)
	//@ ghost slices.CombineAtIndex_Bytes(s.Raw, 0, len(s.Raw), hopOffset, definitions.ReadL1)
	//@ fold acc(s.Mem(), definitions.ReadL1)
	//@ unfold hop.Mem()
	return hop, nil
}

// GetCurrentHopField is a convenience method that returns the current hop field pointed to by the
// CurrHF index in the path meta header.
//@ preserves acc(s.Mem(), definitions.ReadL1)
//@ ensures   r != nil ==> r.ErrorMem()
//@ decreases
func (s *Raw) GetCurrentHopField() (res path.HopField, r error) {
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
//@ requires  0 <= idx
//@ preserves s.Mem()
//@ ensures   r != nil ==> r.ErrorMem()
//@ decreases
func (s *Raw) SetHopField(hop path.HopField, idx int) (r error) {
	//@ share hop
	//@ fold hop.Mem()
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
	//@ ghost slices.SplitByIndex_Bytes(s.Raw, 0, len(s.Raw), hopOffset, writePerm)
	//@ ghost slices.SplitByIndex_Bytes(s.Raw, hopOffset, len(s.Raw), hopOffset+path.HopLen, writePerm)
	//@ ghost slices.Reslice_Bytes(s.Raw, hopOffset, hopOffset+path.HopLen, writePerm)
	ret := hop.SerializeTo(s.Raw[hopOffset : hopOffset+path.HopLen])
	//@ ghost slices.Unslice_Bytes(s.Raw, hopOffset, hopOffset+path.HopLen, writePerm)
	//@ ghost slices.CombineAtIndex_Bytes(s.Raw, hopOffset, len(s.Raw), hopOffset+path.HopLen, writePerm)
	//@ ghost slices.CombineAtIndex_Bytes(s.Raw, 0, len(s.Raw), hopOffset, writePerm)
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
