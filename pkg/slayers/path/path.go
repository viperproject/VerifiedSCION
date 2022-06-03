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

package path

import (
	// "fmt" // no support for globals yet

	//@ "github.com/scionproto/scion/verification/utils/definitions"
	"github.com/scionproto/scion/pkg/private/serrors"
)

// PathType is uint8 so 256 values max.
const maxPathType = 256

// No support for globals yet
/*
var (
	registeredPaths [maxPathType]metadata
	strictDecoding  bool = true
)
*/

// Type indicates the type of the path contained in the SCION header.
type Type uint8

// No support for globals yet
/*
func (t Type) String() string {
	pm := registeredPaths[t]
	if !pm.inUse {
		return fmt.Sprintf("UNKNOWN (%d)", t)
	}
	return fmt.Sprintf("%v (%d)", pm.Desc, t)
}
*/

// TODO:
// - make the functions in Path non partial if possible, make them require
//   the passed slice to have the expected length

// Path is the path contained in the SCION header.
type Path interface {
	//  Must hold in every valid of Path.
	//@ pred Mem()
	//  Must imply the resources required to initialize
	//  a new instance of a predicate.
	//@ pred NonInitMem()
	// SerializeTo serializes the path into the provided buffer.
	//  There are implementations of this interface that modify the underlying
	//  structure when serializing (e.g. scion.Raw)
	//@ preserves Mem() && acc(b)
	//@ decreases
	SerializeTo(b []byte) error
	// DecodesFromBytes decodes the path from the provided buffer.
	//  There are implementations of this interface (e.g. scion.Raw) that store
	//  b and use it as internal data.
	//@ requires NonInitMem()
	//@ requires acc(b)
	//@ ensures  Mem()
	//@ ensures  Mem() --* NonInitMem()
	//@ decreases
	DecodeFromBytes(b []byte) error
	// Reverse reverses a path such that it can be used in the reversed direction.
	//
	// XXX(shitz): This method should possibly be moved to a higher-level path manipulation package.
	//@ requires Mem()
	//@ ensures e == nil ==> Mem()
	//@ decreases
	Reverse() (p Path, e error)
	// Len returns the length of a path in bytes.
	//@ pure
	//@ requires acc(Mem(), _)
	//  ensures l >= 0 // TODO: open issue, this causes exception
	//@ decreases
	Len() (l int)
	// Type returns the type of a path.
	//@ pure
	//@ requires acc(Mem(), _)
	//@ decreases
	Type() Type
}

// (verifiedscion) no support for closures yet
/*
type metadata struct {
	inUse bool
	Metadata
}

// Metadata defines a new SCION path type, used for dynamic SICON path type registration.
type Metadata struct {
	// Type is a unique value for the path.
	Type Type
	// Desc is the description/name of the path.
	Desc string
	// New is a path constructor function.
	New func() Path
}
*/

// RegisterPath registers a new SCION path type globally.
// The PathType passed in must be unique, or a runtime panic will occur.
// No support for globals yet
/*
func RegisterPath(pathMeta Metadata) {
	pm := registeredPaths[pathMeta.Type]
	if pm.inUse {
		panic("path type already registered")
	}
	registeredPaths[pathMeta.Type].inUse = true
	registeredPaths[pathMeta.Type].Metadata = pathMeta
}
*/

// StrictDecoding enables or disables strict path decoding. If enabled, unknown
// path types fail to decode. If disabled, unknown path types are decoded into a
// raw path that keeps the encoded path around for re-serialization.
//
// Strict parsing is enabled by default.
//
// Experimental: This function is experimental and might be subject to change.
/*
func StrictDecoding(strict bool) {
	strictDecoding = strict
}

// NewPath returns a new path object of pathType.
func NewPath(pathType Type) (Path, error) {
	pm := registeredPaths[pathType]
	if !pm.inUse {
		if strictDecoding {
			return nil, serrors.New("unsupported path", "type", pathType)
		}
		return &rawPath{}, nil
	}
	return pm.New(), nil
}
*/

// NewRawPath returns a new raw path that can hold any path type.
func NewRawPath() Path {
	return &rawPath{}
}

type rawPath struct {
	raw      []byte
	pathType Type
}

//@ preserves acc(p.Mem(), definitions.ReadL10) && acc(b)
//@ ensures   e == nil
//@ decreases
func (p *rawPath) SerializeTo(b []byte) (e error) {
	//@ unfold acc(p.Mem(), definitions.ReadL10)
	copy(b, p.raw /*@, definitions.ReadL10 @*/)
	//@ fold acc(p.Mem(), definitions.ReadL10)
	return nil
}

//@ requires p.NonInitMem() && acc(b)
//@ ensures  p.Mem()
//@ ensures  p.Mem() --* p.NonInitMem()
//@ ensures  e == nil
//@ decreases
func (p *rawPath) DecodeFromBytes(b []byte) (e error) {
	//@ unfold p.NonInitMem()
	p.raw = b
	//@ fold p.Mem()
	//@ package p.Mem() --* p.NonInitMem() {
	//@ 	unfold p.Mem()
	//@		fold p.NonInitMem()
	//@ }
	return nil
}

//@ requires p.Mem()
//@ ensures e != nil && e.ErrorMem()
//@ decreases
func (p *rawPath) Reverse() (r Path, e error) {
	return nil, serrors.New("not supported")
}

//@ pure
//@ requires acc(p.Mem(), _)
//@ ensures l >= 0
//@ decreases
func (p *rawPath) Len() (l int) {
	return /*@ unfolding p.Mem() in @*/ len(p.raw)
}

//@ pure
//@ requires acc(p.Mem(), _)
//@ decreases
func (p *rawPath) Type() Type {
	return /*@ unfolding p.Mem() in @*/ p.pathType
}
