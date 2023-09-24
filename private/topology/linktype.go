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
	//@ "github.com/scionproto/scion/verification/utils/slices"
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

//@ decreases
func (l LinkType) String() string {
	if l == Unset {
		return "unset"
	}
	s, err := l.MarshalText()
	if err != nil {
		return err.Error()
	}
	//@ unfold slices.AbsSlice_Bytes(s, 0, len(s))
	return string(s)
}

// LinkTypeFromString returns the numerical link type associated with a string description. If the
// string is not recognized, an Unset link type is returned. The matching is case-insensitive.
//@ decreases
func LinkTypeFromString(s string) (res LinkType) {
	var l /*@@@*/ LinkType
	tmp := []byte(s)
	//@ fold slices.AbsSlice_Bytes(tmp, 0, len(tmp))
	if err := l.UnmarshalText(tmp); err != nil {
		return Unset
	}
	return l
}

//@ ensures (l == Core || l == Parent || l == Child || l == Peer) == (err == nil)
//@ ensures err == nil ==> slices.AbsSlice_Bytes(res, 0, len(res))
//@ ensures err != nil ==> err.ErrorMem()
//@ decreases
func (l LinkType) MarshalText() (res []byte, err error) {
	switch l {
	case Core:
		tmp := []byte("core")
		//@ fold slices.AbsSlice_Bytes(tmp, 0, len(tmp))
		return tmp, nil
	case Parent:
		tmp := []byte("parent")
		//@ fold slices.AbsSlice_Bytes(tmp, 0, len(tmp))
		return tmp, nil
	case Child:
		tmp := []byte("child")
		//@ fold slices.AbsSlice_Bytes(tmp, 0, len(tmp))
		return tmp, nil
	case Peer:
		tmp := []byte("peer")
		//@ fold slices.AbsSlice_Bytes(tmp, 0, len(tmp))
		return tmp, nil
	default:
		return nil, serrors.New("invalid link type")
	}
}

//@ preserves acc(l)
//@ preserves acc(slices.AbsSlice_Bytes(data, 0, len(data)), R15)
//@ ensures   err != nil ==> err.ErrorMem()
//@ decreases
func (l *LinkType) UnmarshalText(data []byte) (err error) {
	//@ unfold acc(slices.AbsSlice_Bytes(data, 0, len(data)), R15)
	//@ ghost defer fold acc(slices.AbsSlice_Bytes(data, 0, len(data)), R15)
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
