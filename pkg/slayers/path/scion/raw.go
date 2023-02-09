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
// @ requires  s.NonInitMem()
// @ preserves slices.AbsSlice_Bytes(data, 0, len(data))
// @ ensures   res == nil ==> s.Mem(data)
// @ ensures   res != nil ==> (s.NonInitMem() && res.ErrorMem())
// @ decreases
func (s *Raw) DecodeFromBytes(data []byte) (res error) {
	//@ unfold s.NonInitMem()
	if err := s.Base.DecodeFromBytes(data); err != nil {
		//@ fold s.NonInitMem()
		return err
	}
	// (VerifiedSCION) Gobra expects a stronger contract for s.Len() when in fact what
	// happens here is that we just call the same function in s.Base.
	pathLen := s. /*@ Base. @*/ Len()
	if len(data) < pathLen {
		//@ apply s.Base.Mem() --* s.Base.NonInitMem()
		//@ fold s.NonInitMem()
		return serrors.New("RawPath raw too short", "expected", pathLen, "actual", int(len(data)))
	}
	s.Raw = data[:pathLen]
	//@ fold s.Mem(data)
	return nil
}

// SerializeTo writes the path to a slice. The slice must be big enough to hold the entire data,
// otherwise an error is returned.
// @ preserves acc(s.Mem(ubuf), def.ReadL1)
// @ preserves slices.AbsSlice_Bytes(ubuf, 0, len(ubuf))
// @ preserves slices.AbsSlice_Bytes(b, 0, len(b))
// @ ensures   r != nil ==> r.ErrorMem()
// @ decreases
func (s *Raw) SerializeTo(b []byte /*@, ghost ubuf []byte @*/) (r error) {
	if /*@ unfolding acc(s.Mem(ubuf), _) in @*/ s.Raw == nil {
		return serrors.New("raw is nil")
	}
	if minLen := s.Len( /*@ ubuf @*/ ); len(b) < minLen {
		return serrors.New("buffer too small", "expected", minLen, "actual", len(b))
	}
	//@ unfold acc(s.Mem(ubuf), def.ReadL1)
	// XXX(roosd): This modifies the underlying buffer. Consider writing to data
	// directly.
	//@ unfold acc(s.Base.Mem(), def.ReadL1)
	//@ slices.SplitRange_Bytes(ubuf, 0, len(s.Raw), writePerm)
	//@ assert slices.AbsSlice_Bytes(s.Raw, 0, len(s.Raw))
	//@ slices.SplitRange_Bytes(s.Raw, 0, MetaLen, writePerm)
	if err := s.PathMeta.SerializeTo(s.Raw[:MetaLen]); err != nil {
		// @ def.Unreachable()
		return err
	}
	//@ fold acc(s.Base.Mem(), def.ReadL1)
	//@ slices.CombineRange_Bytes(s.Raw, 0, MetaLen, writePerm)
	//@ unfold acc(slices.AbsSlice_Bytes(s.Raw, 0, len(s.Raw)), def.ReadL2)
	//@ unfold slices.AbsSlice_Bytes(b, 0, len(b))
	copy(b, s.Raw /*@ , def.ReadL2 @*/)
	//@ fold slices.AbsSlice_Bytes(b, 0, len(b))
	//@ fold acc(slices.AbsSlice_Bytes(s.Raw, 0, len(s.Raw)), def.ReadL2)
	//@ slices.CombineRange_Bytes(ubuf, 0, len(s.Raw), writePerm)
	//@ fold acc(s.Mem(ubuf), def.ReadL1)
	return nil
}

// Reverse reverses the path such that it can be used in the reverse direction.
// @ requires  s.Mem(ubuf)
// @ preserves slices.AbsSlice_Bytes(ubuf, 0, len(ubuf))
// @ ensures   err == nil ==> typeOf(p) == type[*Raw]
// @ ensures   err == nil ==> p != nil && p != (*Raw)(nil)
// @ ensures   err == nil ==> p.Mem(ubuf)
// @ ensures   err != nil ==> err.ErrorMem()
// @ decreases
func (s *Raw) Reverse( /*@ ghost ubuf []byte @*/ ) (p path.Path, err error) {
	// XXX(shitz): The current implementation is not the most performant, since it parses the entire
	// path first. If this becomes a performance bottleneck, the implementation should be changed to
	// work directly on the raw representation.
	decoded, err := s.ToDecoded( /*@ ubuf @*/ )
	if err != nil {
		return nil, err
	}
	reversed, err := decoded.Reverse( /*@ unfolding s.Mem(ubuf) in s.Raw @*/ )
	if err != nil {
		return nil, err
	}
	//@ unfold s.Mem(ubuf)
	//@ slices.SplitRange_Bytes(ubuf, 0, len(s.Raw), writePerm)
	if err := reversed. /*@ (*Decoded). @*/ SerializeTo(s.Raw /*@, s.Raw @*/); err != nil {
		//@ slices.CombineRange_Bytes(ubuf, 0, len(s.Raw), writePerm)
		return nil, err
	}
	//@ ghost sraw := s.Raw
	//@ fold s.Mem(ubuf)
	//@ s.DowngradePerm(ubuf)
	err = s.DecodeFromBytes( /*@ unfolding s.NonInitMem() in @*/ s.Raw)
	//@ slices.CombineRange_Bytes(ubuf, 0, len(sraw), writePerm)
	//@ ghost if err == nil { s.Widen(sraw, ubuf) }
	return s, err
}

// ToDecoded transforms a scion.Raw to a scion.Decoded.
// @ preserves s.Mem(ubuf)
// @ preserves slices.AbsSlice_Bytes(ubuf, 0, len(ubuf))
// @ ensures   err == nil ==> d.Mem(unfolding acc(s.Mem(ubuf), _) in s.Raw)
// @ ensures   err == nil ==> old(unfolding s.Mem(ubuf) in s.Base.InfValid()) ==> unfolding d.Mem(unfolding acc(s.Mem(ubuf), _) in s.Raw) in d.Base.InfValid()
// @ ensures   err != nil ==> err.ErrorMem()
// @ decreases
func (s *Raw) ToDecoded( /*@ ghost ubuf []byte @*/ ) (d *Decoded, err error) {
	//@ s.RawIdxPerm(ubuf, MetaLen, writePerm)
	//@ unfold acc(s.Base.Mem(), def.ReadL1)
	// Serialize PathMeta to ensure potential changes are reflected Raw.
	if err := s.PathMeta.SerializeTo(s.Raw[:MetaLen]); err != nil {
		// @ def.Unreachable()
		return nil, err
	}
	//@ fold acc(s.Base.Mem(), def.ReadL1)
	//@ assert s.Base.InfValid() ==> unfolding acc(s.Base.Mem(), def.ReadL1) in unfolding slices.AbsSlice_Bytes(s.Raw[:MetaLen], 0, len(s.Raw[:MetaLen])) in s.PathMeta.CurrINF == s.Raw[:MetaLen][0] >> 6
	//@ s.UndoRawIdxPerm(ubuf, MetaLen, writePerm)
	decoded := &Decoded{}
	//@ fold decoded.Base.NonInitMem()
	//@ fold decoded.NonInitMem()
	//@ unfold s.Mem(ubuf)
	//@ slices.SplitByIndex_Bytes(ubuf, 0, len(ubuf), len(s.Raw), writePerm)
	//@ slices.Reslice_Bytes(ubuf, 0, len(s.Raw), writePerm)
	if err := decoded.DecodeFromBytes(s.Raw); err != nil {
		//@ slices.Unslice_Bytes(ubuf, 0, len(s.Raw), writePerm)
		//@ slices.CombineAtIndex_Bytes(ubuf, 0, len(ubuf), len(s.Raw), writePerm)
		//@ fold s.Mem(ubuf)
		return nil, err
	}
	//@ slices.Unslice_Bytes(ubuf, 0, len(s.Raw), writePerm)
	//@ slices.CombineAtIndex_Bytes(ubuf, 0, len(ubuf), len(s.Raw), writePerm)
	//@ fold s.Mem(ubuf)
	return decoded, nil
}

// IncPath increments the path and writes it to the buffer.
// @ requires s.Mem(ubuf)
// @ preserves slices.AbsSlice_Bytes(ubuf, 0, len(ubuf))
// @ ensures  old(unfolding s.Mem(ubuf) in unfolding
// @   s.Base.Mem() in (s.NumINF <= 0 || int(s.PathMeta.CurrHF) >= s.NumHops-1)) ==> r != nil
// @ ensures  r == nil ==> s.Mem(ubuf)
// @ ensures  r != nil ==> s.NonInitMem()
// @ ensures  r != nil ==> r.ErrorMem()
// @ decreases
func (s *Raw) IncPath( /*@ ghost ubuf []byte @*/ ) (r error) {
	//@ unfold s.Mem(ubuf)
	if err := s.Base.IncPath(); err != nil {
		//@ fold s.NonInitMem()
		return err
	}
	//@ fold s.Mem(ubuf)
	//@ s.RawIdxPerm(ubuf, MetaLen, writePerm)
	//@ unfold acc(s.Base.Mem(), 1/2)
	err := s.PathMeta.SerializeTo(s.Raw[:MetaLen])
	//@ fold acc(s.Base.Mem(), 1/2)
	//@ s.UndoRawIdxPerm(ubuf, MetaLen, writePerm)
	return err
}

// GetInfoField returns the InfoField at a given index.
// @ requires acc(s.Mem(ubuf), def.ReadL1)
// @ requires 0 <= idx
// @ preserves acc(slices.AbsSlice_Bytes(ubuf, 0, len(ubuf)), def.ReadL1)
// @ ensures  acc(s.Mem(ubuf), def.ReadL1)
// @ ensures  err != nil ==> err.ErrorMem()
// @ decreases
func (s *Raw) GetInfoField(idx int /*@, ghost ubuf []byte @*/) (ifield path.InfoField, err error) {
	//@ unfold acc(s.Mem(ubuf), def.ReadL2)
	//@ unfold acc(s.Base.Mem(), def.ReadL3)
	if idx >= s.NumINF {
		e := serrors.New("InfoField index out of bounds", "max", s.NumINF-1, "actual", idx)
		//@ fold acc(s.Base.Mem(), def.ReadL3)
		//@ fold acc(s.Mem(ubuf), def.ReadL2)
		return path.InfoField{}, e
	}
	//@ fold acc(s.Base.Mem(), def.ReadL3)
	//@ fold acc(s.Mem(ubuf), def.ReadL2)
	infOffset := MetaLen + idx*path.InfoLen
	info /*@@@*/ := path.InfoField{}
	//@ s.RawRangePerm(ubuf, infOffset, infOffset+path.InfoLen, def.ReadL1)
	if err := info.DecodeFromBytes(s.Raw[infOffset : infOffset+path.InfoLen]); err != nil {
		//@ s.UndoRawRangePerm(ubuf, infOffset, infOffset+path.InfoLen, def.ReadL1)
		return path.InfoField{}, err
	}
	//@ s.UndoRawRangePerm(ubuf, infOffset, infOffset+path.InfoLen, def.ReadL1)
	return info, nil
}

// GetCurrentInfoField is a convenience method that returns the current hop field pointed to by the
// CurrINF index in the path meta header.
// @ preserves acc(s.Mem(ubuf), def.ReadL1)
// @ preserves acc(slices.AbsSlice_Bytes(ubuf, 0, len(ubuf)), def.ReadL1)
// @ ensures r != nil ==> r.ErrorMem()
// @ decreases
func (s *Raw) GetCurrentInfoField( /*@ ghost ubuf []byte @*/ ) (res path.InfoField, r error) {
	//@ unfold acc(s.Mem(ubuf), def.ReadL1)
	//@ unfold acc(s.Base.Mem(), def.ReadL1)
	idx := int(s.PathMeta.CurrINF)
	// (VerifiedSCION) Cannot assert bounds of uint:
	// https://github.com/viperproject/gobra/issues/192
	//@ assume 0 <= idx
	//@ fold acc(s.Base.Mem(), def.ReadL1)
	//@ fold acc(s.Mem(ubuf), def.ReadL1)
	return s.GetInfoField(idx /*@, ubuf @*/)
}

// SetInfoField updates the InfoField at a given index.
// @ requires  0 <= idx
// @ preserves acc(s.Mem(ubuf), def.ReadL20)
// @ preserves slices.AbsSlice_Bytes(ubuf, 0, len(ubuf))
// @ ensures   r != nil ==> r.ErrorMem()
// @ decreases
func (s *Raw) SetInfoField(info path.InfoField, idx int /*@, ghost ubuf []byte @*/) (r error) {
	//@ share info
	//@ unfold acc(s.Mem(ubuf), def.ReadL20)
	//@ unfold acc(s.Base.Mem(), def.ReadL20)
	if idx >= s.NumINF {
		err := serrors.New("InfoField index out of bounds", "max", s.NumINF-1, "actual", idx)
		//@ fold acc(s.Base.Mem(), def.ReadL20)
		//@ fold acc(s.Mem(ubuf), def.ReadL20)
		return err
	}
	infOffset := MetaLen + idx*path.InfoLen
	//@ slices.SplitRange_Bytes(ubuf, 0, len(s.Raw), writePerm)
	//@ assert slices.AbsSlice_Bytes(s.Raw, 0, len(s.Raw))
	//@ slices.SplitRange_Bytes(s.Raw, infOffset, infOffset+path.InfoLen, writePerm)
	ret := info.SerializeTo(s.Raw[infOffset : infOffset+path.InfoLen])
	//@ slices.CombineRange_Bytes(s.Raw, infOffset, infOffset+path.InfoLen, writePerm)
	//@ slices.CombineRange_Bytes(ubuf, 0, len(s.Raw), writePerm)
	//@ fold acc(s.Base.Mem(), def.ReadL20)
	//@ fold acc(s.Mem(ubuf), def.ReadL20)
	return ret
}

// GetHopField returns the HopField at a given index.
// @ requires  0 <= idx
// @ preserves acc(s.Mem(ubuf), def.ReadL1)
// @ preserves acc(slices.AbsSlice_Bytes(ubuf, 0, len(ubuf)), def.ReadL1)
// @ ensures   r != nil ==> r.ErrorMem()
// @ decreases
func (s *Raw) GetHopField(idx int /*@, ghost ubuf []byte @*/) (res path.HopField, r error) {
	//@ unfold acc(s.Mem(ubuf), def.ReadL2)
	//@ unfold acc(s.Base.Mem(), def.ReadL3)
	if idx >= s.NumHops {
		err := serrors.New("HopField index out of bounds", "max", s.NumHops-1, "actual", idx)
		//@ fold acc(s.Base.Mem(), def.ReadL3)
		//@ fold acc(s.Mem(ubuf), def.ReadL2)
		return path.HopField{}, err
	}
	hopOffset := MetaLen + s.NumINF*path.InfoLen + idx*path.HopLen
	//@ fold acc(s.Base.Mem(), def.ReadL3)
	//@ fold acc(s.Mem(ubuf), def.ReadL2)
	hop /*@@@*/ := path.HopField{}
	//@ s.RawRangePerm(ubuf, hopOffset, hopOffset+path.HopLen, def.ReadL2)
	if err := hop.DecodeFromBytes(s.Raw[hopOffset : hopOffset+path.HopLen]); err != nil {
		//@ s.UndoRawRangePerm(ubuf, hopOffset, hopOffset+path.HopLen, writePerm)
		return path.HopField{}, err
	}
	//@ s.UndoRawRangePerm(ubuf, hopOffset, hopOffset+path.HopLen, def.ReadL2)
	//@ unfold hop.Mem()
	return hop, nil
}

// GetCurrentHopField is a convenience method that returns the current hop field pointed to by the
// CurrHF index in the path meta header.
// @ preserves acc(s.Mem(ubuf), def.ReadL1)
// @ preserves acc(slices.AbsSlice_Bytes(ubuf, 0, len(ubuf)), def.ReadL1)
// @ ensures   r != nil ==> r.ErrorMem()
// @ decreases
func (s *Raw) GetCurrentHopField( /*@ ghost ubuf []byte @*/ ) (res path.HopField, r error) {
	//@ unfold acc(s.Mem(ubuf), def.ReadL2)
	//@ unfold acc(s.Base.Mem(), def.ReadL3)
	idx := int(s.PathMeta.CurrHF)
	// (VerifiedSCION) Cannot assert bounds of uint:
	// https://github.com/viperproject/gobra/issues/192
	//@ assume 0 <= idx
	//@ fold acc(s.Base.Mem(), def.ReadL3)
	//@ fold acc(s.Mem(ubuf), def.ReadL2)
	return s.GetHopField(idx /*@, ubuf @*/)
}

// SetHopField updates the HopField at a given index.
// @ requires  0 <= idx
// @ preserves acc(s.Mem(ubuf), def.ReadL20)
// @ preserves slices.AbsSlice_Bytes(ubuf, 0, len(ubuf))
// @ ensures   r != nil ==> r.ErrorMem()
// @ decreases
func (s *Raw) SetHopField(hop path.HopField, idx int /*@, ghost ubuf []byte @*/) (r error) {
	//@ share hop
	// (VerifiedSCION) Cannot assert bounds of uint:
	// https://github.com/viperproject/gobra/issues/192
	//@ assume 0 <= hop.ConsIngress && 0 <= hop.ConsEgress
	//@ fold hop.Mem()
	//@ unfold acc(s.Mem(ubuf), def.ReadL20)
	//@ unfold acc(s.Base.Mem(), def.ReadL20)
	if idx >= s.NumHops {
		// (gavin) introduced `err`
		err := serrors.New("HopField index out of bounds", "max", s.NumHops-1, "actual", idx)
		//@ fold acc(s.Base.Mem(), def.ReadL20)
		//@ fold acc(s.Mem(ubuf), def.ReadL20)
		return err
	}
	hopOffset := MetaLen + s.NumINF*path.InfoLen + idx*path.HopLen
	//@ slices.SplitRange_Bytes(ubuf, 0, len(s.Raw), writePerm)
	//@ assert slices.AbsSlice_Bytes(s.Raw, 0, len(s.Raw))
	//@ slices.SplitRange_Bytes(s.Raw, hopOffset, hopOffset+path.HopLen, writePerm)
	ret := hop.SerializeTo(s.Raw[hopOffset : hopOffset+path.HopLen])
	//@ slices.CombineRange_Bytes(s.Raw, hopOffset, hopOffset+path.HopLen, writePerm)
	//@ slices.CombineRange_Bytes(ubuf, 0, len(s.Raw), writePerm)
	//@ fold acc(s.Base.Mem(), def.ReadL20)
	//@ fold acc(s.Mem(ubuf), def.ReadL20)
	return ret
}

// IsFirstHop returns whether the current hop is the first hop on the path.
// @ preserves acc(s.Mem(ubuf), def.ReadL1)
// @ decreases
func (s *Raw) IsFirstHop( /*@ ghost ubuf []byte @*/ ) bool {
	//@ unfold acc(s.Mem(ubuf), def.ReadL2)
	//@ defer  fold acc(s.Mem(ubuf), def.ReadL2)
	//@ unfold acc(s.Base.Mem(), def.ReadL3)
	//@ defer  fold acc(s.Base.Mem(), def.ReadL3)
	return s.PathMeta.CurrHF == 0
}

// IsPenultimateHop returns whether the current hop is the penultimate hop on the path.
// @ preserves acc(s.Mem(ubuf), def.ReadL1)
// @ decreases
func (s *Raw) IsPenultimateHop( /*@ ghost ubuf []byte @*/ ) bool {
	//@ unfold acc(s.Mem(ubuf), def.ReadL2)
	//@ defer  fold acc(s.Mem(ubuf), def.ReadL2)
	//@ unfold acc(s.Base.Mem(), def.ReadL3)
	//@ defer  fold acc(s.Base.Mem(), def.ReadL3)
	return int(s.PathMeta.CurrHF) == (s.NumHops - 2)
}

// IsLastHop returns whether the current hop is the last hop on the path.
// @ preserves acc(s.Mem(ubuf), def.ReadL1)
// @ decreases
func (s *Raw) IsLastHop( /*@ ghost ubuf []byte @*/ ) bool {
	//@ unfold acc(s.Mem(ubuf), def.ReadL2)
	//@ defer  fold acc(s.Mem(ubuf), def.ReadL2)
	//@ unfold acc(s.Base.Mem(), def.ReadL3)
	//@ defer  fold acc(s.Base.Mem(), def.ReadL3)
	return int(s.PathMeta.CurrHF) == (s.NumHops - 1)
}
