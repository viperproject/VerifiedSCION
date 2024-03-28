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
	// @ "encoding/binary"
	"github.com/scionproto/scion/pkg/private/serrors"
	"github.com/scionproto/scion/pkg/slayers/path"
	//@ . "github.com/scionproto/scion/verification/utils/definitions"
	//@ sl "github.com/scionproto/scion/verification/utils/slices"
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
// @ preserves acc(sl.AbsSlice_Bytes(data, 0, len(data)), R40)
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
		//@ s.Base.DowngradePerm()
		//@ fold s.NonInitMem()
		return serrors.New("RawPath raw too short", "expected", pathLen, "actual", int(len(data)))
	}
	s.Raw = data[:pathLen]
	//@ fold s.Mem(data)
	return nil
}

// SerializeTo writes the path to a slice. The slice must be big enough to hold the entire data,
// otherwise an error is returned.
// @ preserves acc(s.Mem(ubuf), R1)
// @ preserves sl.AbsSlice_Bytes(ubuf, 0, len(ubuf))
// @ preserves sl.AbsSlice_Bytes(b, 0, len(b))
// @ ensures   r != nil ==> r.ErrorMem()
// @ decreases
func (s *Raw) SerializeTo(b []byte /*@, ghost ubuf []byte @*/) (r error) {
	if /*@ unfolding acc(s.Mem(ubuf), _) in @*/ s.Raw == nil {
		return serrors.New("raw is nil")
	}
	if minLen := s.Len( /*@ ubuf @*/ ); len(b) < minLen {
		return serrors.New("buffer too small", "expected", minLen, "actual", len(b))
	}
	//@ unfold acc(s.Mem(ubuf), R1)
	// XXX(roosd): This modifies the underlying buffer. Consider writing to data
	// directly.
	//@ unfold acc(s.Base.Mem(), R1)
	//@ sl.SplitRange_Bytes(ubuf, 0, len(s.Raw), writePerm)
	//@ assert sl.AbsSlice_Bytes(s.Raw, 0, len(s.Raw))
	//@ sl.SplitRange_Bytes(s.Raw, 0, MetaLen, writePerm)
	if err := s.PathMeta.SerializeTo(s.Raw[:MetaLen]); err != nil {
		// @ Unreachable()
		return err
	}
	//@ fold acc(s.Base.Mem(), R1)
	//@ sl.CombineRange_Bytes(s.Raw, 0, MetaLen, writePerm)
	//@ unfold acc(sl.AbsSlice_Bytes(s.Raw, 0, len(s.Raw)), R2)
	//@ unfold sl.AbsSlice_Bytes(b, 0, len(b))
	copy(b, s.Raw /*@ , R2 @*/)
	//@ fold sl.AbsSlice_Bytes(b, 0, len(b))
	//@ fold acc(sl.AbsSlice_Bytes(s.Raw, 0, len(s.Raw)), R2)
	//@ sl.CombineRange_Bytes(ubuf, 0, len(s.Raw), writePerm)
	//@ fold acc(s.Mem(ubuf), R1)
	return nil
}

// Reverse reverses the path such that it can be used in the reverse direction.
// @ requires  s.Mem(ubuf)
// @ preserves sl.AbsSlice_Bytes(ubuf, 0, len(ubuf))
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
	//@ sl.SplitRange_Bytes(ubuf, 0, len(s.Raw), writePerm)
	if err := reversed. /*@ (*Decoded). @*/ SerializeTo(s.Raw /*@, s.Raw @*/); err != nil {
		//@ sl.CombineRange_Bytes(ubuf, 0, len(s.Raw), writePerm)
		return nil, err
	}
	//@ ghost sraw := s.Raw
	//@ fold s.Mem(ubuf)
	//@ s.DowngradePerm(ubuf)
	err = s.DecodeFromBytes( /*@ unfolding s.NonInitMem() in @*/ s.Raw)
	//@ sl.CombineRange_Bytes(ubuf, 0, len(sraw), writePerm)
	//@ ghost if err == nil { s.Widen(sraw, ubuf) }
	return s, err
}

// ToDecoded transforms a scion.Raw to a scion.Decoded.
// @ preserves acc(s.Mem(ubuf), R5)
// @ preserves sl.AbsSlice_Bytes(ubuf, 0, len(ubuf))
// @ ensures   err == nil ==> (
// @ 	let newUb := s.RawBufferMem(ubuf) in
// @ 	d.Mem(newUb) &&
// @ 	(old(s.ValidCurrIdxs(ubuf)) ==> d.ValidCurrIdxs(newUb)))
// @ ensures   err != nil ==> err.ErrorMem()
// @ decreases
func (s *Raw) ToDecoded( /*@ ghost ubuf []byte @*/ ) (d *Decoded, err error) {
	//@ unfold acc(s.Mem(ubuf), R6)
	//@ unfold acc(s.Base.Mem(), R6)
	//@ ghost var base Base = s.Base
	//@ ghost var pathMeta MetaHdr = s.Base.PathMeta
	//@ ghost validIdxs := s.ValidCurrIdxs(ubuf)
	//@ assert validIdxs ==> s.Base.PathMeta.InBounds()
	//@ assert validIdxs ==> base.ValidCurrIdxsSpec()
	//@ assert s.Raw[:MetaLen] === ubuf[:MetaLen]

	// (VerifiedSCION) In this method, many slice operations are done in two
	// steps to preserve framming information.
	//@ sl.SplitRange_Bytes(ubuf, 0, MetaLen, HalfPerm)
	//@ sl.SplitRange_Bytes(ubuf, 0, MetaLen, HalfPerm)
	// Serialize PathMeta to ensure potential changes are reflected Raw.
	if err := s.PathMeta.SerializeTo(s.Raw[:MetaLen]); err != nil {
		// @ Unreachable()
		return nil, err
	}
	//@ ghost b0 := (unfolding acc(sl.AbsSlice_Bytes(s.Raw[:MetaLen], 0, MetaLen), _) in s.Raw[0])
	//@ ghost b1 := (unfolding acc(sl.AbsSlice_Bytes(s.Raw[:MetaLen], 0, MetaLen), _) in s.Raw[1])
	//@ ghost b2 := (unfolding acc(sl.AbsSlice_Bytes(s.Raw[:MetaLen], 0, MetaLen), _) in s.Raw[2])
	//@ ghost b3 := (unfolding acc(sl.AbsSlice_Bytes(s.Raw[:MetaLen], 0, MetaLen), _) in s.Raw[3])
	//@ assert let line := s.PathMeta.SerializedToLine() in binary.BigEndian.PutUint32Spec(b0, b1, b2, b3, line)
	//@ sl.CombineRange_Bytes(ubuf, 0, MetaLen, HalfPerm)
	//@ assert &ubuf[0] == &s.Raw[:MetaLen][0]
	//@ assert &ubuf[1] == &s.Raw[:MetaLen][1]
	//@ assert &ubuf[2] == &s.Raw[:MetaLen][2]
	//@ assert &ubuf[3] == &s.Raw[:MetaLen][3]
	//@ assert b0 == (unfolding acc(sl.AbsSlice_Bytes(s.Raw[:MetaLen], 0, MetaLen), _) in ubuf[0])
	//  (VerifiedSCION): for some reason, silicon requires the following line to be able to prove
	//  bX == ubuf[X].
	//@ assert unfolding acc(sl.AbsSlice_Bytes(s.Raw[:MetaLen], 0, MetaLen), _) in
	//@ 	(ubuf[0] == (unfolding acc(sl.AbsSlice_Bytes(ubuf, 0, len(ubuf)), _) in ubuf[0]))
	//@ sl.CombineRange_Bytes(ubuf, 0, MetaLen, HalfPerm)
	decoded := &Decoded{}
	//@ fold decoded.Base.NonInitMem()
	//@ fold decoded.NonInitMem()
	//@ sl.SplitByIndex_Bytes(ubuf, 0, len(ubuf), len(s.Raw), HalfPerm)
	//@ assert unfolding acc(sl.AbsSlice_Bytes(ubuf, 0, len(ubuf)), _) in
	//@ 	(ubuf[0] == (unfolding acc(sl.AbsSlice_Bytes(ubuf, 0, len(s.Raw)), _) in ubuf[0]))
	//@ sl.SplitByIndex_Bytes(ubuf, 0, len(ubuf), len(s.Raw), HalfPerm)
	//@ sl.Reslice_Bytes(ubuf, 0, len(s.Raw), HalfPerm)
	//@ assert &ubuf[0] == &ubuf[:len(s.Raw)][0]
	//@ assert &ubuf[1] == &ubuf[:len(s.Raw)][1]
	//@ assert &ubuf[2] == &ubuf[:len(s.Raw)][2]
	//@ assert &ubuf[3] == &ubuf[:len(s.Raw)][3]
	//@ assert unfolding acc(sl.AbsSlice_Bytes(ubuf[:len(s.Raw)], 0, len(s.Raw)), _) in
	//@ 	(ubuf[0] == (unfolding acc(sl.AbsSlice_Bytes(ubuf, 0, len(s.Raw)), _) in ubuf[0]))
	//@ assert b0 == (unfolding acc(sl.AbsSlice_Bytes(ubuf, 0, len(s.Raw)), _) in ubuf[0])
	//@ assert b1 == (unfolding acc(sl.AbsSlice_Bytes(ubuf, 0, len(s.Raw)), _) in ubuf[1])
	//@ assert b2 == (unfolding acc(sl.AbsSlice_Bytes(ubuf, 0, len(s.Raw)), _) in ubuf[2])
	//@ assert b3 == (unfolding acc(sl.AbsSlice_Bytes(ubuf, 0, len(s.Raw)), _) in ubuf[3])
	//@ sl.Reslice_Bytes(ubuf, 0, len(s.Raw), HalfPerm)
	if err := decoded.DecodeFromBytes(s.Raw); err != nil {
		//@ sl.Unslice_Bytes(ubuf, 0, len(s.Raw), writePerm)
		//@ sl.CombineAtIndex_Bytes(ubuf, 0, len(ubuf), len(s.Raw), writePerm)
		//@ fold acc(s.Base.Mem(), R6)
		//@ fold acc(s.Mem(ubuf), R6)
		return nil, err
	}
	//@ ghost lenR := len(s.Raw) // TODO: move to the top and rewrite body
	//@ ghost if validIdxs {
	//@ 	s.PathMeta.SerializeAndDeserializeLemma(b0, b1, b2, b3)
	//@ 	assert pathMeta == decoded.GetMetaHdr(s.Raw)
	//@ 	assert decoded.GetBase(s.Raw).ValidCurrIdxsSpec()
	//@ 	assert decoded.ValidCurrIdxs(s.Raw)
	//@ }
	//@ sl.Unslice_Bytes(ubuf, 0, len(s.Raw), HalfPerm)
	//@ sl.Unslice_Bytes(ubuf, 0, len(s.Raw), HalfPerm)
	//@ sl.CombineAtIndex_Bytes(ubuf, 0, len(ubuf), len(s.Raw), HalfPerm)
	//@ sl.CombineAtIndex_Bytes(ubuf, 0, len(ubuf), len(s.Raw), HalfPerm)
	//@ fold acc(s.Base.Mem(), R6)
	//@ fold acc(s.Mem(ubuf), R6)
	return decoded, nil
}

// IncPath increments the path and writes it to the buffer.
// @ requires s.Mem(ubuf)
// @ preserves sl.AbsSlice_Bytes(ubuf, 0, len(ubuf))
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
// @ requires  acc(s.Mem(ubuf), R10)
// @ requires  0 <= idx
// @ preserves acc(sl.AbsSlice_Bytes(ubuf, 0, len(ubuf)), R10)
// @ ensures   acc(s.Mem(ubuf), R10)
// @ ensures   (idx < old(s.GetNumINF(ubuf))) == (err == nil)
// @ ensures   err != nil ==> err.ErrorMem()
// @ decreases
func (s *Raw) GetInfoField(idx int /*@, ghost ubuf []byte @*/) (ifield path.InfoField, err error) {
	//@ unfold acc(s.Mem(ubuf), R10)
	//@ unfold acc(s.Base.Mem(), R11)
	if idx >= s.NumINF {
		e := serrors.New("InfoField index out of bounds", "max", s.NumINF-1, "actual", idx)
		//@ fold acc(s.Base.Mem(), R11)
		//@ fold acc(s.Mem(ubuf), R10)
		return path.InfoField{}, e
	}
	//@ fold acc(s.Base.Mem(), R11)
	//@ fold acc(s.Mem(ubuf), R10)
	infOffset := MetaLen + idx*path.InfoLen
	info /*@@@*/ := path.InfoField{}
	//@ s.RawRangePerm(ubuf, infOffset, infOffset+path.InfoLen, R10)
	if err := info.DecodeFromBytes(s.Raw[infOffset : infOffset+path.InfoLen]); err != nil {
		//@ Unreachable()
		return path.InfoField{}, err
	}
	//@ s.UndoRawRangePerm(ubuf, infOffset, infOffset+path.InfoLen, R10)
	return info, nil
}

// GetCurrentInfoField is a convenience method that returns the current hop field pointed to by the
// CurrINF index in the path meta header.
// @ preserves acc(s.Mem(ubuf), R8)
// @ preserves acc(sl.AbsSlice_Bytes(ubuf, 0, len(ubuf)), R2)
// @ ensures   (r == nil) == (s.GetCurrINF(ubuf) < s.GetNumINF(ubuf))
// @ ensures   r != nil ==> r.ErrorMem()
// @ decreases
func (s *Raw) GetCurrentInfoField( /*@ ghost ubuf []byte @*/ ) (res path.InfoField, r error) {
	//@ unfold acc(s.Mem(ubuf), R9)
	//@ unfold acc(s.Base.Mem(), R10)
	idx := int(s.PathMeta.CurrINF)
	// (VerifiedSCION) Cannot assert bounds of uint:
	// https://github.com/viperproject/gobra/issues/192
	//@ assume 0 <= idx
	//@ fold acc(s.Base.Mem(), R10)
	//@ fold acc(s.Mem(ubuf), R9)
	return s.GetInfoField(idx /*@, ubuf @*/)
}

// SetInfoField updates the InfoField at a given index.
// @ requires  0 <= idx
// @ preserves acc(s.Mem(ubuf), R20)
// @ preserves sl.AbsSlice_Bytes(ubuf, 0, len(ubuf))
// @ ensures   r != nil ==> r.ErrorMem()
// @ decreases
func (s *Raw) SetInfoField(info path.InfoField, idx int /*@, ghost ubuf []byte @*/) (r error) {
	//@ share info
	//@ unfold acc(s.Mem(ubuf), R20)
	//@ unfold acc(s.Base.Mem(), R20)
	if idx >= s.NumINF {
		err := serrors.New("InfoField index out of bounds", "max", s.NumINF-1, "actual", idx)
		//@ fold acc(s.Base.Mem(), R20)
		//@ fold acc(s.Mem(ubuf), R20)
		return err
	}
	infOffset := MetaLen + idx*path.InfoLen
	//@ sl.SplitRange_Bytes(ubuf, 0, len(s.Raw), writePerm)
	//@ assert sl.AbsSlice_Bytes(s.Raw, 0, len(s.Raw))
	//@ sl.SplitRange_Bytes(s.Raw, infOffset, infOffset+path.InfoLen, writePerm)
	ret := info.SerializeTo(s.Raw[infOffset : infOffset+path.InfoLen])
	//@ sl.CombineRange_Bytes(s.Raw, infOffset, infOffset+path.InfoLen, writePerm)
	//@ sl.CombineRange_Bytes(ubuf, 0, len(s.Raw), writePerm)
	//@ fold acc(s.Base.Mem(), R20)
	//@ fold acc(s.Mem(ubuf), R20)
	return ret
}

// GetHopField returns the HopField at a given index.
// @ requires  0 <= idx
// @ preserves acc(s.Mem(ubuf), R10)
// @ preserves acc(sl.AbsSlice_Bytes(ubuf, 0, len(ubuf)), R10)
// @ ensures   (idx < old(s.GetNumHops(ubuf))) == (r == nil)
// @ ensures   r != nil ==> r.ErrorMem()
// @ decreases
func (s *Raw) GetHopField(idx int /*@, ghost ubuf []byte @*/) (res path.HopField, r error) {
	//@ unfold acc(s.Mem(ubuf), R10)
	//@ unfold acc(s.Base.Mem(), R11)
	if idx >= s.NumHops {
		err := serrors.New("HopField index out of bounds", "max", s.NumHops-1, "actual", idx)
		//@ fold acc(s.Base.Mem(), R11)
		//@ fold acc(s.Mem(ubuf), R10)
		return path.HopField{}, err
	}
	hopOffset := MetaLen + s.NumINF*path.InfoLen + idx*path.HopLen
	//@ fold acc(s.Base.Mem(), R11)
	//@ fold acc(s.Mem(ubuf), R10)
	hop /*@@@*/ := path.HopField{}
	//@ s.RawRangePerm(ubuf, hopOffset, hopOffset+path.HopLen, R10)
	if err := hop.DecodeFromBytes(s.Raw[hopOffset : hopOffset+path.HopLen]); err != nil {
		//@ Unreachable()
		return path.HopField{}, err
	}
	//@ s.UndoRawRangePerm(ubuf, hopOffset, hopOffset+path.HopLen, R10)
	//@ unfold hop.Mem()
	return hop, nil
}

// GetCurrentHopField is a convenience method that returns the current hop field pointed to by the
// CurrHF index in the path meta header.
// @ preserves acc(s.Mem(ubuf), R8)
// @ preserves acc(sl.AbsSlice_Bytes(ubuf, 0, len(ubuf)), R2)
// @ ensures   (r == nil) == (s.GetCurrHF(ubuf) < s.GetNumHops(ubuf))
// @ ensures   r != nil ==> r.ErrorMem()
// @ decreases
func (s *Raw) GetCurrentHopField( /*@ ghost ubuf []byte @*/ ) (res path.HopField, r error) {
	//@ unfold acc(s.Mem(ubuf), R9)
	//@ unfold acc(s.Base.Mem(), R10)
	idx := int(s.PathMeta.CurrHF)
	// (VerifiedSCION) Cannot assert bounds of uint:
	// https://github.com/viperproject/gobra/issues/192
	//@ assume 0 <= idx
	//@ fold acc(s.Base.Mem(), R10)
	//@ fold acc(s.Mem(ubuf), R9)
	return s.GetHopField(idx /*@, ubuf @*/)
}

// SetHopField updates the HopField at a given index.
// @ requires  0 <= idx
// @ preserves acc(s.Mem(ubuf), R20)
// @ preserves sl.AbsSlice_Bytes(ubuf, 0, len(ubuf))
// @ ensures   r != nil ==> r.ErrorMem()
// @ decreases
func (s *Raw) SetHopField(hop path.HopField, idx int /*@, ghost ubuf []byte @*/) (r error) {
	//@ share hop
	// (VerifiedSCION) Cannot assert bounds of uint:
	// https://github.com/viperproject/gobra/issues/192
	//@ assume 0 <= hop.ConsIngress && 0 <= hop.ConsEgress
	//@ fold hop.Mem()
	//@ unfold acc(s.Mem(ubuf), R20)
	//@ unfold acc(s.Base.Mem(), R20)
	if idx >= s.NumHops {
		// (gavin) introduced `err`
		err := serrors.New("HopField index out of bounds", "max", s.NumHops-1, "actual", idx)
		//@ fold acc(s.Base.Mem(), R20)
		//@ fold acc(s.Mem(ubuf), R20)
		return err
	}
	hopOffset := MetaLen + s.NumINF*path.InfoLen + idx*path.HopLen
	//@ sl.SplitRange_Bytes(ubuf, 0, len(s.Raw), writePerm)
	//@ assert sl.AbsSlice_Bytes(s.Raw, 0, len(s.Raw))
	//@ sl.SplitRange_Bytes(s.Raw, hopOffset, hopOffset+path.HopLen, writePerm)
	ret := hop.SerializeTo(s.Raw[hopOffset : hopOffset+path.HopLen])
	//@ sl.CombineRange_Bytes(s.Raw, hopOffset, hopOffset+path.HopLen, writePerm)
	//@ sl.CombineRange_Bytes(ubuf, 0, len(s.Raw), writePerm)
	//@ fold acc(s.Base.Mem(), R20)
	//@ fold acc(s.Mem(ubuf), R20)
	return ret
}

// IsFirstHop returns whether the current hop is the first hop on the path.
// @ pure
// @ requires  acc(s.Mem(ubuf), _)
// @ decreases
func (s *Raw) IsFirstHop( /*@ ghost ubuf []byte @*/ ) bool {
	return /*@ unfolding acc(s.Mem(ubuf), _) in (unfolding acc(s.Base.Mem(), _) in @*/ s.PathMeta.CurrHF == 0 /*@ ) @*/
}

// IsPenultimateHop returns whether the current hop is the penultimate hop on the path.
// @ preserves acc(s.Mem(ubuf), R20)
// @ decreases
func (s *Raw) IsPenultimateHop( /*@ ghost ubuf []byte @*/ ) bool {
	//@ unfold acc(s.Mem(ubuf), R20)
	//@ defer  fold acc(s.Mem(ubuf), R20)
	//@ unfold acc(s.Base.Mem(), R20)
	//@ defer  fold acc(s.Base.Mem(), R20)
	return int(s.PathMeta.CurrHF) == (s.NumHops - 2)
}

// IsLastHop returns whether the current hop is the last hop on the path.
// @ preserves acc(s.Mem(ubuf), R20)
// @ decreases
func (s *Raw) IsLastHop( /*@ ghost ubuf []byte @*/ ) bool {
	//@ unfold acc(s.Mem(ubuf), R20)
	//@ defer  fold acc(s.Mem(ubuf), R20)
	//@ unfold acc(s.Base.Mem(), R20)
	//@ defer  fold acc(s.Base.Mem(), R20)
	return int(s.PathMeta.CurrHF) == (s.NumHops - 1)
}
