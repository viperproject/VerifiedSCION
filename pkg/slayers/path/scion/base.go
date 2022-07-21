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
	//@ "github.com/scionproto/scion/verification/utils/definitions"
)

// MetaLen is the length of the PathMetaHeader.
const MetaLen = 4

const PathType path.Type = 1

/*
func RegisterPath() {
	path.RegisterPath(path.Metadata{
		Type: PathType,
		Desc: "SCION",
		New: func() path.Path {
			return &Raw{}
		},
	})
}
*/

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

//@ requires  s.NonInitMem()
//@ requires  len(data) >= MetaLen
//@ preserves acc(data, definitions.ReadL10)
//@ ensures r != nil ==> (s.NonInitMem() && r.ErrorMem())
//@ ensures r == nil ==> s.Mem()
//@ decreases
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
	//@ invariant -1 <= i && i <= 2
	//@ invariant acc(s)
	//@ invariant 0 <= s.NumHops && 0 <= s.NumINF && s.NumINF <= 3
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
		//  Cannot assert bounds of uint:
		//  https://github.com/viperproject/gobra/issues/192
		//@ assume int(s.PathMeta.SegLen[i]) >= 0
		s.NumHops += int(s.PathMeta.SegLen[i])
	}
	//@ fold s.Mem()
	return nil
}

// IncPath increases the currHF index and currINF index if appropriate.
//@ requires s.Mem()
//@ requires unfolding s.Mem() in s.NumINF > 0
//@ requires unfolding s.Mem() in int(s.PathMeta.CurrHF) < s.NumHops-1
//@ ensures  s.Mem()
//@ ensures  s.Len() == old(s.Len())
//@ ensures  e == nil
//@ decreases
func (s *Base) IncPath() (e error) {
	//@ unfold s.Mem()
	if s.NumINF == 0 {
		return serrors.New("empty path cannot be increased")
	}
	if int(s.PathMeta.CurrHF) >= s.NumHops-1 {
		s.PathMeta.CurrHF = uint8(s.NumHops - 1)
		return serrors.New("path already at end")
	}
	s.PathMeta.CurrHF++
	// Update CurrINF
	s.PathMeta.CurrINF = s.infIndexForHF(s.PathMeta.CurrHF)
	//@ fold s.Mem()
	return nil
}

// IsXover returns whether we are at a crossover point.
//@ preserves acc(s.Mem(), definitions.ReadL10)
//@ decreases
func (s *Base) IsXover() (r bool) {
	//@ unfold acc(s.Mem(), definitions.ReadL10)
	r = s.PathMeta.CurrINF != s.infIndexForHF(s.PathMeta.CurrHF+1)
	//@ fold acc(s.Mem(), definitions.ReadL10)
	return r
}

//@ preserves acc(s, definitions.ReadL11)
//@ preserves 0 <= s.NumINF && s.NumINF <= 3 && 0 <= s.NumHops
//@ ensures   0 < s.NumINF ==> (0 <= r && r < s.NumINF)
//@ decreases
func (s *Base) infIndexForHF(hf uint8) (r uint8) {
	left := uint8(0)
	//@ invariant acc(s, definitions.ReadL11)
	//@ invariant s.NumINF >= 0 && s.NumINF <= 3 && s.NumHops >= 0
	//@ invariant 0 <= i && i <= 3
	//@ decreases s.NumINF-i
	for i := 0; i < s.NumINF; i++ {
		if hf >= left {
			if hf < left+s.PathMeta.SegLen[i] {
				return uint8(i)
			}
		}
		left += s.PathMeta.SegLen[i]
	}
	// at the end we just return the last index.
	return uint8(s.NumINF - 1)
}

// Len returns the length of the path in bytes.
//@ pure
//@ requires acc(s.Mem(), _)
//@ ensures r >= MetaLen
//@ ensures r == (unfolding acc(s.Mem(), _) in (MetaLen + int(s.NumINF)*path.InfoLen + int(s.NumHops)*path.HopLen))
//@ decreases
func (s *Base) Len() (r int) {
	return /*@ unfolding acc(s.Mem(), _) in @*/ MetaLen + s.NumINF*path.InfoLen + s.NumHops*path.HopLen
}

// Type returns the type of the path.
//@ pure
//@ ensures t == PathType
//@ decreases
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
//@ requires len(raw) >= MetaLen
//@ preserves acc(m) && acc(raw, definitions.ReadL10)
//@ ensures m.CurrINF >= 0 && m.CurrHF >= 0
//@ ensures e == nil
//@ decreases
func (m *MetaHdr) DecodeFromBytes(raw []byte) (e error) {
	if len(raw) < MetaLen {
		return serrors.New("MetaHdr raw too short", "expected", MetaLen, "actual", len(raw))
	}
	line := binary.BigEndian.Uint32(raw)
	m.CurrINF = uint8(line >> 30)
	m.CurrHF = uint8(line>>24) & 0x3F
	//  The following assumption is guaranteed by Go but still
	//  not modeled in Gobra.
	//@ assume m.CurrINF >= 0 && m.CurrHF >= 0
	m.SegLen[0] = uint8(line>>12) & 0x3F
	m.SegLen[1] = uint8(line>>6) & 0x3F
	m.SegLen[2] = uint8(line) & 0x3F

	return nil
}

// SerializeTo writes the fields into the provided buffer. The buffer must be of length >=
// scion.MetaLen.
//@ requires len(b) >= MetaLen
//@ preserves acc(m, definitions.ReadL10) && acc(b)
//@ ensures e == nil
//@ decreases
func (m *MetaHdr) SerializeTo(b []byte) (e error) {
	if len(b) < MetaLen {
		return serrors.New("buffer for MetaHdr too short", "expected", MetaLen, "actual", len(b))
	}
	line := uint32(m.CurrINF)<<30 | uint32(m.CurrHF&0x3F)<<24
	line |= uint32(m.SegLen[0]&0x3F) << 12
	line |= uint32(m.SegLen[1]&0x3F) << 6
	line |= uint32(m.SegLen[2] & 0x3F)
	binary.BigEndian.PutUint32(b, line)

	return nil
}

//  The spec of fmt.Sprintf is still too limited to verify this method.
//@ trusted
//@ decreases
func (m MetaHdr) String() string {
	return fmt.Sprintf("{CurrInf: %d, CurrHF: %d, SegLen: %v}", m.CurrINF, m.CurrHF, m.SegLen)
}
