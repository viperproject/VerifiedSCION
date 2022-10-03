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
	// (VerifiedSCION) this field is meant to be a ghost field
	// which identifies from where the Path was decoded.
	// XXX(gavinleroy) this field should be marked as 'ghost' when
	// ghost fields are supported by Gobra.
	//@ underlyingBuf []byte
	// (VerifiedSCION) this field is meant to be a ghost field
	// indicating how many prefix bytes 'Raw' is of 'underlyingBuf'.
	//@ dataLen int
	Raw []byte
}

// DecodeFromBytes only decodes the PathMetaHeader. Otherwise the nothing is decoded and simply kept
// as raw bytes.
//@ requires s.NonInitMem()
//@ requires 0 <= dataLen && dataLen <= len(underlyingBuf)
//@ requires len(data) == dataLen
//@ requires data === underlyingBuf[:dataLen]
//@ requires slices.AbsSlice_Bytes(underlyingBuf, 0, len(underlyingBuf))
//@ ensures  res == nil ==> s.Mem()
//@ ensures  res == nil ==> s.GetUnderlyingBuf() === underlyingBuf
//@ ensures  res != nil ==> (s.NonInitMem() && res.ErrorMem())
//@ ensures  res != nil ==> slices.AbsSlice_Bytes(underlyingBuf, 0, len(underlyingBuf))
//@ decreases
func (s *Raw) DecodeFromBytes(data []byte /*@, underlyingBuf []byte, dataLen int @*/) (res error) {
	//@ ghost slices.SplitByIndex_Bytes(underlyingBuf, 0, len(underlyingBuf), dataLen, writePerm)
	//@ ghost slices.Reslice_Bytes(underlyingBuf, 0, dataLen, writePerm)
	//@ assert acc(slices.AbsSlice_Bytes(data, 0, len(data)), writePerm)
	//@ unfold s.NonInitMem()
	if err := s.Base.DecodeFromBytes(data); err != nil {
		//@ ghost slices.Unslice_Bytes(underlyingBuf, 0, dataLen, writePerm)
		//@ ghost slices.CombineAtIndex_Bytes(underlyingBuf, 0, len(underlyingBuf), dataLen, writePerm)
		//@ fold s.NonInitMem()
		return err
	}
	// (VerifiedSCION) Gobra expects a stronger contract for s.Len() when in fact
	// what happens here is that we just call the same function in s.Base.
	pathLen := s. /*@ Base. @*/ Len()
	if len(data) < pathLen {
		//@ apply s.Base.Mem() --* s.Base.NonInitMem()
		//@ fold s.NonInitMem()
		//@ ghost slices.Unslice_Bytes(underlyingBuf, 0, dataLen, writePerm)
		//@ ghost slices.CombineAtIndex_Bytes(underlyingBuf, 0, len(underlyingBuf), dataLen, writePerm)
		return serrors.New("RawPath raw too short", "expected", pathLen, "actual", int(len(data)))
	}
	//@ assert dataLen >= pathLen
	//@ assert data === underlyingBuf[:dataLen]
	//@ assert data[:pathLen] === underlyingBuf[:dataLen][:pathLen]
	//@ assert data[:pathLen] === underlyingBuf[:pathLen]
	//@ ghost slices.Unslice_Bytes(underlyingBuf, 0, dataLen, writePerm)
	//@ ghost slices.CombineAtIndex_Bytes(underlyingBuf, 0, len(underlyingBuf), dataLen, writePerm)
	//@ s.underlyingBuf = underlyingBuf
	//@ s.dataLen = pathLen
	//@ ghost slices.SplitByIndex_Bytes(underlyingBuf, 0, len(underlyingBuf), pathLen, writePerm)
	//@ ghost slices.Reslice_Bytes(underlyingBuf, 0, pathLen, writePerm)
	//@ assert data[:pathLen] === underlyingBuf[:pathLen]
	//@ unfold slices.AbsSlice_Bytes(data[:pathLen], 0, len(data[:pathLen]))
	s.Raw = data[:pathLen]
	//@ fold slices.AbsSlice_Bytes(s.Raw, 0, len(s.Raw))
	//@ fold s.Mem()
	return nil
}

// SerializeTo writes the path to a slice. The slice must be big enough to hold the entire data,
// otherwise an error is returned.
//@ preserves s.Mem()
//@ preserves s.GetUnderlyingBuf() === underlyingBuf
//@ preserves slices.AbsSlice_Bytes(b, 0, len(b))
//@ requires 0 <= dataLen && dataLen <= len(underlyingBuf)
//@ requires  len(b) == dataLen
//@ ensures   r != nil ==> r.ErrorMem()
//@ decreases
func (s *Raw) SerializeTo(b []byte /*@, underlyingBuf []byte, dataLen int @*/) (r error) {
	if /*@ unfolding acc(s.Mem(), _) in @*/ s.Raw == nil {
		return serrors.New("raw is nil")
	}
	if minLen := s.Len(); len(b) < minLen {
		return serrors.New("buffer too small", "expected", minLen, "actual", int(len(b)))
	}
	//@ unfold s.Mem()
	//@ unfold s.Base.Mem()
	//@ ghost slices.SplitByIndex_Bytes(s.Raw, 0, len(s.Raw), MetaLen, writePerm)
	//@ ghost slices.Reslice_Bytes(s.Raw, 0, MetaLen, writePerm)
	// XXX(roosd): This modifies the underlying buffer. Consider writing to data
	// directly.
	if err := s.PathMeta.SerializeTo(s.Raw[:MetaLen]); err != nil {
		//@ ghost slices.Unslice_Bytes(s.Raw, 0, MetaLen, writePerm)
		//@ ghost slices.CombineAtIndex_Bytes(s.Raw, 0, len(b), MetaLen, writePerm)
		//@ ghost slices.Unslice_Bytes(underlyingBuf, 0, dataLen, writePerm)
		//@ ghost slices.CombineAtIndex_Bytes(underlyingBuf, 0, len(underlyingBuf), dataLen, writePerm)
		//@ fold s.Base.Mem()
		//@ fold s.Mem()
		return err
	}
	//@ ghost slices.Unslice_Bytes(s.Raw, 0, MetaLen, writePerm)
	//@ ghost slices.CombineAtIndex_Bytes(s.Raw, 0, len(s.Raw), MetaLen, writePerm)
	//@ assert slices.AbsSlice_Bytes(s.Raw, 0, len(s.Raw))
	//@ preserves acc(&s.Raw, definitions.ReadL1)
	//@ preserves 0 <= dataLen && dataLen <= len(underlyingBuf)
	//@ preserves acc(slices.AbsSlice_Bytes(s.Raw, 0, len(s.Raw)), definitions.ReadL1)
	//@ preserves slices.AbsSlice_Bytes(b, 0, len(b))
	//@ ensures len(s.Raw) == before(len(s.Raw))
	//@ ensures s.Raw === before(s.Raw)
	//@ decreases
	//@ outline(
	//@ unfold acc(slices.AbsSlice_Bytes(s.Raw, 0, len(s.Raw)), definitions.ReadL2)
	//@ unfold slices.AbsSlice_Bytes(b, 0, len(b))
	copy(b, s.Raw /*@ , definitions.ReadL2 @*/)
	//@ fold slices.AbsSlice_Bytes(b, 0, len(b))
	//@ fold acc(slices.AbsSlice_Bytes(s.Raw, 0, len(s.Raw)), definitions.ReadL2)
	//@ )
	//@ fold s.Base.Mem()
	//@ fold s.Mem()
	return nil
}

// Reverse reverses the path such that it can be used in the reverse direction.
//@ requires s.Mem()
//@ ensures  err == nil ==> p != nil
//@ ensures  err == nil ==> typeOf(p) == type[*Raw]
//@ ensures  err == nil ==> p.Mem()
//@ ensures  err == nil ==> p.GetUnderlyingBuf() === old(s.GetUnderlyingBuf())
//@ ensures  err != nil ==> err.ErrorMem()
//@ decreases
func (s *Raw) Reverse() (p path.Path, err error) {
	// XXX(shitz): The current implementation is not the most performant, since it parses the entire
	// path first. If this becomes a performance bottleneck, the implementation should be changed to
	// work directly on the raw representation.
	//@ underlyingBuf := unfolding acc(s.Mem(), _) in s.underlyingBuf
	//@ pathLen := unfolding acc(s.Mem(), _) in s.dataLen
	decoded, err := s.ToDecoded()
	if err != nil {
		return nil, err
	}
	//@ unfold s.NonInitMem()
	//@ assert underlyingBuf === decoded.GetUnderlyingBuf()
	//@ assert s.Raw === underlyingBuf[:pathLen]
	//@ assert underlyingBuf === s.underlyingBuf
	reversed, err := decoded.Reverse()
	if err != nil {
		return nil, err
	}
	//@ assert typeOf(reversed) == type[*Decoded]
	// TODO(VerifiedSCION) remove the extra variable
	var rev *Decoded
	rev = reversed.(*Decoded)
	//@ assert s.Raw === underlyingBuf[:pathLen]
	//@ assert underlyingBuf === rev.GetUnderlyingBuf()
	//@ assert underlyingBuf === s.underlyingBuf
	if err := rev.SerializeTo(s.Raw /*@, underlyingBuf, pathLen @*/); err != nil {
		return nil, err
	}
	//@ unfold rev.Mem()
	//@ assert slices.AbsSlice_Bytes(underlyingBuf, 0, len(underlyingBuf))
	//@ assert underlyingBuf[:pathLen] === s.Raw
	//@ fold s.NonInitMem()
	err = s.DecodeFromBytes( /*@ unfolding acc(s.NonInitMem(), _) in @*/ s.Raw /*@, underlyingBuf, pathLen @*/)
	return s, err
}

// ToDecoded transforms a scion.Raw to a scion.Decoded.
//@ requires s.Mem()
//@ ensures  err == nil ==> d.Mem()
//@ ensures  err == nil ==> s.NonInitMem()
//@ ensures  err == nil ==> unfolding acc(s.NonInitMem(), _) in s.Raw === old(unfolding acc(s.Mem(), _) in s.Raw)
//@ ensures  err == nil ==> unfolding acc(s.NonInitMem(), _) in s.underlyingBuf === old(unfolding acc(s.Mem(), _) in s.underlyingBuf)
//@ ensures  err == nil ==> unfolding acc(s.NonInitMem(), _) in s.dataLen === old(unfolding acc(s.Mem(), _) in s.dataLen)
//@ ensures  err == nil ==> d.GetUnderlyingBuf() === old(s.GetUnderlyingBuf())
//@ ensures  err != nil ==> (s.Mem() && err.ErrorMem())
//@ decreases
func (s *Raw) ToDecoded() (d *Decoded, err error) {
	//@ underlyingBuf := s.GetUnderlyingBuf()
	//@ unfold s.Mem()
	//@ assert underlyingBuf === s.underlyingBuf
	//@ unfold acc(s.Base.Mem(), definitions.ReadL1)
	//@ ghost slices.SplitByIndex_Bytes(s.Raw, 0, len(s.Raw), MetaLen, writePerm)
	//@ requires acc(&s.Raw)
	//@ requires slices.AbsSlice_Bytes(s.Raw, 0, MetaLen)
	//@ requires MetaLen <= len(s.Raw)
	//@ requires  slices.AbsSlice_Bytes(s.Raw, MetaLen, len(s.Raw))
	//@ ensures  acc(&s.Raw)
	//@ ensures s.Raw === before(s.Raw)
	//@ ensures  MetaLen <= len(s.Raw)
	//@ ensures  slices.AbsSlice_Bytes(s.Raw, MetaLen, len(s.Raw))
	//@ ensures  slices.AbsSlice_Bytes(s.Raw[:MetaLen], 0, len(s.Raw[:MetaLen]))
	//@ decreases
	//@ outline(
	//@ ghost slices.Reslice_Bytes(s.Raw, 0, MetaLen, writePerm)
	//@ )
	// Serialize PathMeta to ensure potential changes are reflected Raw.
	if err := s.PathMeta.SerializeTo(s.Raw[:MetaLen]); err != nil {
		//@ ghost slices.Unslice_Bytes(s.Raw, 0, MetaLen, writePerm)
		//@ ghost slices.CombineAtIndex_Bytes(s.Raw, 0, len(s.Raw), MetaLen, writePerm)
		//@ fold acc(s.Base.Mem(), definitions.ReadL1)
		//@ fold s.Mem()
		return nil, err
	}
	//@ ensures decoded.NonInitMem()
	//@ decreases
	//@ outline(
	decoded := &Decoded{}
	//@ fold decoded.Base.NonInitMem()
	//@ fold decoded.NonInitMem()
	//@ )
	//@ fold acc(s.Base.Mem(), definitions.ReadL1)
	//@ ghost slices.Unslice_Bytes(s.Raw, 0, MetaLen, writePerm)
	//@ ghost slices.CombineAtIndex_Bytes(s.Raw, 0, len(s.Raw), MetaLen, writePerm)
	//@ ghost slices.Unslice_Bytes(s.underlyingBuf, 0, s.dataLen, writePerm)
	//@ ghost slices.CombineAtIndex_Bytes(s.underlyingBuf, 0, len(s.underlyingBuf), s.dataLen, writePerm)
	//@ assert s.Raw === s.underlyingBuf[:s.dataLen]
	//@ assert slices.AbsSlice_Bytes(s.underlyingBuf, 0, len(s.underlyingBuf))
	if err := decoded.DecodeFromBytes(s.Raw /*@, s.underlyingBuf, s.dataLen @*/); err != nil {
		//@ ghost slices.SplitByIndex_Bytes(s.underlyingBuf, 0, len(s.underlyingBuf), s.dataLen, writePerm)
		//@ ghost slices.Reslice_Bytes(s.underlyingBuf, 0, s.dataLen, writePerm)
		//@ fold s.Mem()
		return nil, err
	}
	//@ ghost if err == nil {
	//@   assert decoded.GetUnderlyingBuf() === s.underlyingBuf
	//@   assert underlyingBuf === s.underlyingBuf
	//@   unfold s.Base.Mem()
	//@   fold s.Base.NonInitMem()
	//@   fold s.NonInitMem()
	//@ }
	return decoded, nil
}

// IncPath increments the path and writes it to the buffer.
//@ requires s.Mem()
//@ ensures old(unfolding s.Mem() in unfolding
//@   s.Base.Mem() in (s.NumINF <= 0 || int(s.PathMeta.CurrHF) >= s.NumHops-1)) ==> r != nil
//@ ensures  r == nil ==> s.Mem()
//@ ensures  r != nil ==> s.NonInitMem()
//@ ensures  r != nil ==> r.ErrorMem()
//@ decreases
func (s *Raw) IncPath() (r error) {
	//@ unfold s.Mem()
	if err := s.Base.IncPath(); err != nil {
		//@ fold s.NonInitMem()
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
	//@ unfold acc(s.Mem(), definitions.ReadL2)
	//@ unfold acc(s.Base.Mem(), definitions.ReadL3)
	if idx >= s.NumINF {
		e := serrors.New("InfoField index out of bounds", "max", s.NumINF-1, "actual", idx)
		//@ fold acc(s.Base.Mem(), definitions.ReadL3)
		//@ fold acc(s.Mem(), definitions.ReadL2)
		return path.InfoField{}, e
	}
	//@ fold acc(s.Base.Mem(), definitions.ReadL3)
	infOffset := MetaLen + idx*path.InfoLen
	info /*@@@*/ := path.InfoField{}
	//@ ghost slices.SplitByIndex_Bytes(s.Raw, 0, len(s.Raw), infOffset, definitions.ReadL2)
	//@ ghost slices.SplitByIndex_Bytes(s.Raw, infOffset, len(s.Raw), infOffset+path.InfoLen, definitions.ReadL2)
	//@ ghost slices.Reslice_Bytes(s.Raw, infOffset, infOffset+path.InfoLen, definitions.ReadL2)
	if err := info.DecodeFromBytes(s.Raw[infOffset : infOffset+path.InfoLen]); err != nil {
		//@ ghost slices.Unslice_Bytes(s.Raw, infOffset, infOffset+path.InfoLen, definitions.ReadL2)
		//@ ghost slices.CombineAtIndex_Bytes(s.Raw, infOffset, len(s.Raw), infOffset+path.InfoLen, definitions.ReadL2)
		//@ ghost slices.CombineAtIndex_Bytes(s.Raw, 0, len(s.Raw), infOffset, definitions.ReadL2)
		//@ fold acc(s.Mem(), definitions.ReadL2)
		return path.InfoField{}, err
	}
	//@ ghost slices.Unslice_Bytes(s.Raw, infOffset, infOffset+path.InfoLen, definitions.ReadL2)
	//@ ghost slices.CombineAtIndex_Bytes(s.Raw, infOffset, len(s.Raw), infOffset+path.InfoLen, definitions.ReadL2)
	//@ ghost slices.CombineAtIndex_Bytes(s.Raw, 0, len(s.Raw), infOffset, definitions.ReadL2)
	//@ fold acc(s.Mem(), definitions.ReadL2)
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
	idx := int(s.PathMeta.CurrINF)
	// (VerifiedSCION) Cannot assert bounds of uint:
	// https://github.com/viperproject/gobra/issues/192
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
	//@ unfold acc(s.Base.Mem(), definitions.ReadL1)
	if idx >= s.NumINF {
		err := serrors.New("InfoField index out of bounds", "max", s.NumINF-1, "actual", idx)
		//@ fold acc(s.Base.Mem(), definitions.ReadL1)
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
	//@ fold acc(s.Base.Mem(), definitions.ReadL1)
	//@ fold s.Mem()
	return ret
}

// GetHopField returns the HopField at a given index.
//@ requires  0 <= idx
//@ preserves acc(s.Mem(), definitions.ReadL1)
//@ ensures   r != nil ==> r.ErrorMem()
//@ decreases
func (s *Raw) GetHopField(idx int) (res path.HopField, r error) {
	//@ unfold acc(s.Mem(), definitions.ReadL2)
	//@ unfold acc(s.Base.Mem(), definitions.ReadL3)
	if idx >= s.NumHops {
		err := serrors.New("HopField index out of bounds", "max", s.NumHops-1, "actual", idx)
		//@ fold acc(s.Base.Mem(), definitions.ReadL3)
		//@ fold acc(s.Mem(), definitions.ReadL2)
		return path.HopField{}, err
	}
	hopOffset := MetaLen + s.NumINF*path.InfoLen + idx*path.HopLen
	//@ fold acc(s.Base.Mem(), definitions.ReadL3)
	hop /*@@@*/ := path.HopField{}
	//@ ghost slices.SplitByIndex_Bytes(s.Raw, 0, len(s.Raw), hopOffset, definitions.ReadL2)
	//@ ghost slices.SplitByIndex_Bytes(s.Raw, hopOffset, len(s.Raw), hopOffset+path.HopLen, definitions.ReadL2)
	//@ ghost slices.Reslice_Bytes(s.Raw, hopOffset, hopOffset+path.HopLen, definitions.ReadL2)
	if err := hop.DecodeFromBytes(s.Raw[hopOffset : hopOffset+path.HopLen]); err != nil {
		//@ ghost slices.Unslice_Bytes(s.Raw, hopOffset, hopOffset+path.HopLen, definitions.ReadL2)
		//@ ghost slices.CombineAtIndex_Bytes(s.Raw, hopOffset, len(s.Raw), hopOffset+path.HopLen, definitions.ReadL2)
		//@ ghost slices.CombineAtIndex_Bytes(s.Raw, 0, len(s.Raw), hopOffset, definitions.ReadL2)
		//@ fold acc(s.Mem(), definitions.ReadL2)
		return path.HopField{}, err
	}
	//@ ghost slices.Unslice_Bytes(s.Raw, hopOffset, hopOffset+path.HopLen, definitions.ReadL2)
	//@ ghost slices.CombineAtIndex_Bytes(s.Raw, hopOffset, len(s.Raw), hopOffset+path.HopLen, definitions.ReadL2)
	//@ ghost slices.CombineAtIndex_Bytes(s.Raw, 0, len(s.Raw), hopOffset, definitions.ReadL2)
	//@ fold acc(s.Mem(), definitions.ReadL2)
	//@ unfold hop.Mem()
	return hop, nil
}

// GetCurrentHopField is a convenience method that returns the current hop field pointed to by the
// CurrHF index in the path meta header.
//@ preserves acc(s.Mem(), definitions.ReadL1)
//@ ensures   r != nil ==> r.ErrorMem()
//@ decreases
func (s *Raw) GetCurrentHopField() (res path.HopField, r error) {
	//@ unfold acc(s.Mem(), definitions.ReadL2)
	//@ unfold acc(s.Base.Mem(), definitions.ReadL3)
	idx := int(s.PathMeta.CurrHF)
	// (VerifiedSCION) Cannot assert bounds of uint:
	// https://github.com/viperproject/gobra/issues/192
	//@ assume 0 <= idx
	//@ fold acc(s.Base.Mem(), definitions.ReadL3)
	//@ fold acc(s.Mem(), definitions.ReadL2)
	return s.GetHopField(idx)
}

// SetHopField updates the HopField at a given index.
//@ requires  0 <= idx
//@ preserves s.Mem()
//@ ensures   r != nil ==> r.ErrorMem()
//@ decreases
func (s *Raw) SetHopField(hop path.HopField, idx int) (r error) {
	//@ share hop
	// (VerifiedSCION) Cannot assert bounds of uint:
	// https://github.com/viperproject/gobra/issues/192
	//@ assume 0 <= hop.ConsIngress && 0 <= hop.ConsEgress
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
	//@ unfold acc(s.Mem(), definitions.ReadL2)
	//@ unfold acc(s.Base.Mem(), definitions.ReadL3)
	numberHops := s.NumHops
	currentHop := int(s.PathMeta.CurrHF)
	//@ fold acc(s.Base.Mem(), definitions.ReadL3)
	//@ fold acc(s.Mem(), definitions.ReadL2)
	return currentHop == numberHops-2
}

// IsLastHop returns whether the current hop is the last hop on the path.
//@ preserves acc(s.Mem(), definitions.ReadL1)
//@ decreases
func (s *Raw) IsLastHop() bool {
	//@ unfold acc(s.Mem(), definitions.ReadL2)
	//@ unfold acc(s.Base.Mem(), definitions.ReadL3)
	numberHops := s.NumHops
	currentHop := int(s.PathMeta.CurrHF)
	//@ fold acc(s.Base.Mem(), definitions.ReadL3)
	//@ fold acc(s.Mem(), definitions.ReadL2)
	return currentHop == numberHops-1
}
