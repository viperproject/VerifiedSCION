// Copyright 2016 ETH Zurich
// Copyright 2018 ETH Zurich, Anapaya Systems
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

package addr

import (
	"fmt"
	"strconv"
	"strings"

	"github.com/scionproto/scion/pkg/private/serrors"
)

const (
	IABytes       = 8
	ISDBits       = 16
	ASBits        = 48
	BGPASBits     = 32
	MaxISD    ISD = (1 << ISDBits) - 1
	MaxAS     AS  = (1 << ASBits) - 1
	MaxBGPAS  AS  = (1 << BGPASBits) - 1

	asPartBits = 16
	asPartBase = 16
	asPartMask = (1 << asPartBits) - 1
	asParts    = ASBits / asPartBits
)

// ISD is the ISolation Domain identifier. See formatting and allocations here:
// https://github.com/scionproto/scion/wiki/ISD-and-AS-numbering#isd-numbers
type ISD uint16

// ParseISD parses an ISD from a decimal string. Note that ISD 0 is parsed
// without any errors.
// @ trusted
// @ requires false
func ParseISD(s string) (ISD, error) {
	isd, err := strconv.ParseUint(s, 10, ISDBits)
	if err != nil {
		return 0, serrors.WrapStr("parsing ISD", err)
	}
	return ISD(isd), nil
}

// @ trusted
// @ requires false
func (isd ISD) String() string {
	return strconv.FormatUint(uint64(isd), 10)
}

//var _ encoding.TextUnmarshaler = (*AS)(nil)

// AS is the Autonomous System identifier. See formatting and allocations here:
// https://github.com/scionproto/scion/wiki/ISD-and-AS-numbering#as_-numbers
type AS uint64

// ParseAS parses an AS from a decimal (in the case of the 32bit BGP AS number
// space) or ipv6-style hex (in the case of SCION-only AS numbers) string.
// @ trusted
// @ requires false
func ParseAS(as_ string) (AS, error) {
	return parseAS(as_, ":")
}

// @ trusted
// @ requires false
func parseAS(as_ string, sep string) (AS, error) {
	parts := strings.Split(as_, sep)
	if len(parts) == 1 {
		// Must be a BGP AS, parse as_ 32-bit decimal number
		return asParseBGP(as_)
	}

	if len(parts) != asParts {
		return 0, serrors.New("wrong number of separators", "sep", sep, "value", as_)
	}
	var parsed AS
	for i := 0; i < asParts; i++ {
		parsed <<= asPartBits
		v, err := strconv.ParseUint(parts[i], asPartBase, asPartBits)
		if err != nil {
			return 0, serrors.WrapStr("parsing AS part", err, "index", i, "value", as_)
		}
		parsed |= AS(v)
	}
	// This should not be reachable. However, we leave it here to protect
	// against future refactor mistakes.
	if !parsed.inRange() {
		return 0, serrors.New("AS out of range", "max", MaxAS, "value", as_)
	}
	return parsed, nil
}

// @ trusted
// @ requires false
func asParseBGP(s string) (AS, error) {
	as_, err := strconv.ParseUint(s, 10, BGPASBits)
	if err != nil {
		return 0, serrors.WrapStr("parsing BGP AS", err)
	}
	return AS(as_), nil
}

// @ trusted
// @ requires false
func (as_ AS) String() string {
	return fmtAS(as_, ":")
}

// @ trusted
// @ requires false
func (as_ AS) inRange() bool {
	return as_ <= MaxAS
}

// @ trusted
// @ requires false
func (as_ AS) MarshalText() ([]byte, error) {
	if !as_.inRange() {
		return nil, serrors.New("AS out of range", "max", MaxAS, "value", as_)
	}
	return []byte(as_.String()), nil
}

// @ trusted
// @ requires false
func (as_ *AS) UnmarshalText(text []byte) error {
	parsed, err := ParseAS(string(text))
	if err != nil {
		return err
	}
	*as_ = parsed
	return nil
}

// var _ fmt.Stringer = IA(0)
// var _ encoding.TextUnmarshaler = (*IA)(nil)
// var _ flag.Value = (*IA)(nil)

// IA represents the ISD (ISolation Domain) and AS (Autonomous System) Id of a given SCION AS.
// The highest 16 bit form the ISD number and the lower 48 bits form the AS number.
type IA uint64

// MustIAFrom creates an IA from the ISD and AS number. It panics if any error
// is encountered. Callers must ensure that the values passed to this function
// are valid.
// @ trusted
// @ requires false
func MustIAFrom(isd ISD, as_ AS) IA {
	ia, err := IAFrom(isd, as_)
	if err != nil {
		panic(fmt.Sprintf("parsing ISD-AS: %s", err))
	}
	return ia
}

// IAFrom creates an IA from the ISD and AS number.
// @ trusted
// @ requires false
func IAFrom(isd ISD, as_ AS) (IA, error) {
	if !as_.inRange() {
		return 0, serrors.New("AS out of range", "max", MaxAS, "value", as_)
	}
	return IA(isd)<<ASBits | IA(as_&MaxAS), nil
}

// ParseIA parses an IA from a string of the format 'isd-as_'.
// @ trusted
// @ requires false
func ParseIA(ia string) (IA, error) {
	parts := strings.Split(ia, "-")
	if len(parts) != 2 {
		return 0, serrors.New("invalid ISD-AS", "value", ia)
	}
	isd, err := ParseISD(parts[0])
	if err != nil {
		return 0, err
	}
	as_, err := ParseAS(parts[1])
	if err != nil {
		return 0, err
	}
	return MustIAFrom(isd, as_), nil
}

// @ trusted
// @ requires false
func (ia IA) ISD() ISD {
	return ISD(ia >> ASBits)
}

// @ trusted
// @ requires false
func (ia IA) AS() AS {
	return AS(ia) & MaxAS
}

// @ trusted
// @ requires false
func (ia IA) MarshalText() ([]byte, error) {
	return []byte(ia.String()), nil
}

// @ trusted
// @ requires false
func (ia *IA) UnmarshalText(b []byte) error {
	parsed, err := ParseIA(string(b))
	if err != nil {
		return err
	}
	*ia = parsed
	return nil
}

// @ trusted
// @ requires false
func (ia IA) IsZero() bool {
	return ia == 0
}

// @ trusted
// @ requires false
func (ia IA) Equal(other IA) bool {
	return ia == other
}

// IsWildcard returns whether the ia has a wildcard part (isd or as_).
// @ trusted
// @ requires false
func (ia IA) IsWildcard() bool {
	return ia.ISD() == 0 || ia.AS() == 0
}

// @ trusted
// @ requires false
func (ia IA) String() string {
	return fmt.Sprintf("%d-%s", ia.ISD(), ia.AS())
}

// Set implements flag.Value interface
// @ trusted
// @ requires false
func (ia *IA) Set(s string) error {
	pIA, err := ParseIA(s)
	if err != nil {
		return err
	}
	*ia = pIA
	return nil
}
