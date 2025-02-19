// Copyright 2017 ETH Zurich
// Copyright 2019 ETH Zurich, Anapaya Systems
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

package topology

import (
	"strings"

	"github.com/scionproto/scion/pkg/private/serrors"
	//@ . "github.com/scionproto/scion/verification/utils/definitions"
	//@ sl "github.com/scionproto/scion/verification/utils/slices"
)

// LinkType describes inter-AS links.
type LinkType int

// XXX(scrye): These constants might end up in files or on the network, so they should not
// change. They are defined here s.t. they are not subject to the protobuf generator.

const (
	// Unset is used for unknown link types.
	Unset LinkType = 0
	// Core links connect core ASes.
	Core LinkType = 1
	// Parent links are configured on non-core links pointing towards the core of an ISD.
	Parent LinkType = 2
	// Child links are configured on non-core links pointing away from the core of an ISD.
	Child LinkType = 3
	// Peer links are configured for peering relationships.
	Peer LinkType = 4
)

// @ decreases
func (l LinkType) String() string {
	if l == Unset {
		return "unset"
	}
	s, err := l.MarshalText()
	if err != nil {
		return err.Error()
	}

	return string(s)
}

// LinkTypeFromString returns the numerical link type associated with a string description. If the
// string is not recognized, an Unset link type is returned. The matching is case-insensitive.
// @ decreases
func LinkTypeFromString(s string) (res LinkType) {
	var l /*@@@*/ LinkType
	tmp := []byte(s)

	if err := l.UnmarshalText(tmp); err != nil {
		return Unset
	}
	return l
}

// @ ensures (l == Core || l == Parent || l == Child || l == Peer) == (err == nil)
// @ ensures err == nil ==> 0 <= 0 && 0 <= len(res) && len(res) <= cap(res) && forall i int :: { &res[i] } 0 <= i && i < len(res) ==> acc(&res[i])
// @ ensures err != nil ==> err.ErrorMem()
// @ decreases
func (l LinkType) MarshalText() (res []byte, err error) {
	switch l {
	case Core:
		tmp := []byte("core")

		return tmp, nil
	case Parent:
		tmp := []byte("parent")

		return tmp, nil
	case Child:
		tmp := []byte("child")

		return tmp, nil
	case Peer:
		tmp := []byte("peer")

		return tmp, nil
	default:
		return nil, serrors.New("invalid link type")
	}
}

// @ preserves acc(l)
// @ preserves 0 <= 0 && 0 <= len(data) && len(data) <= cap(data) && forall i int :: { &data[i] } 0 <= i && i < len(data) ==> acc(&data[i], R15)
// @ ensures   err != nil ==> err.ErrorMem()
// @ decreases
func (l *LinkType) UnmarshalText(data []byte) (err error) {


	switch strings.ToLower(string(data)) {
	case "core":
		*l = Core
	case "parent":
		*l = Parent
	case "child":
		*l = Child
	case "peer":
		*l = Peer
	default:
		return serrors.New("invalid link type", "linkType", string(data))
	}
	return nil
}
