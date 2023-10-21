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

// @ initEnsures PathPackageMem()
// Skipped the following post-condition due to performance reasons
// initEnsures forall t Type :: 0 <= t && t < maxPathType ==> !Registered(t)
// Instead, we have:
// @ initEnsures !Registered(0) && !Registered(1) && !Registered(2) && !Registered(3)
package path

import (
	"fmt"

	"github.com/scionproto/scion/pkg/private/serrors"
	//@ . "github.com/scionproto/scion/verification/utils/definitions"
	//@ sl "github.com/scionproto/scion/verification/utils/slices"
)

// PathType is uint8 so 256 values max.
const maxPathType = 256

var (
	registeredPaths/*@@@*/ [maxPathType]metadata
	strictDecoding/*@@@*/ bool = true
)

func init() {
	// (VerifiedSCION) ghost initialization code to establish the PathPackageMem predicate.
	// @ assert acc(&registeredPaths)
	// @ assert acc(&strictDecoding)
	// @ assert forall t Type :: { registeredPaths[t] } 0 <= t && t < maxPathType ==> !registeredPaths[t].inUse
	// @ fold PathPackageMem()
}

// Type indicates the type of the path contained in the SCION header.
type Type uint8

// @ requires 0 <= t && t < maxPathType
// @ preserves acc(PathPackageMem(), R20)
// @ decreases
func (t Type) String() string {
	//@ unfold acc(PathPackageMem(), R20)
	//@ ghost defer fold acc(PathPackageMem(), R20)
	pm := registeredPaths[t]
	if !pm.inUse {
		return fmt.Sprintf("UNKNOWN (%d)", t)
	}
	return fmt.Sprintf("%v (%d)", pm.Desc, t)
}

// Path is the path contained in the SCION header.
type Path interface {
	// (VerifiedSCION) Must hold for every valid Path.
	//@ pred Mem()

	// (VerifiedSCION) Must imply the resources required to initialize
	// a new instance of a predicate.
	//@ pred NonInitMem() // TODO: In the end, check if it is still necessary

	// (VerifiedSCION) Must apply to every Path after initialization
	//@ ghost
	//@ requires acc(Mem(), _)
	//@ decreases
	//@ pure Valid(ghost ub []byte) bool // TODO: rename to 'DecodedFrom'

	// SerializeTo serializes the path into the provided buffer.
	// (VerifiedSCION) There are implementations of this interface that modify the underlying
	// structure when serializing (e.g. scion.Raw)
	//@ preserves sl.AbsSlice_Bytes(ub, 0, len(ub))
	//@ preserves acc(Mem(), R1) && Valid(ub)
	//@ preserves sl.AbsSlice_Bytes(b, 0, len(b))
	//@ ensures   e != nil ==> e.ErrorMem()
	//@ decreases
	SerializeTo(b []byte /*@, ghost ub []byte @*/) (e error)
	// DecodesFromBytes decodes the path from the provided buffer.
	//@ requires  NonInitMem()
	//@ preserves sl.AbsSlice_Bytes(b, 0, len(b))
	//@ ensures   err == nil ==> (Mem() && Valid(b))
	//@ ensures   err != nil ==> err.ErrorMem()
	//@ ensures   err != nil ==> NonInitMem()
	//@ decreases
	DecodeFromBytes(b []byte) (err error)
	// Reverse reverses a path such that it can be used in the reversed direction.
	// XXX(shitz): This method should possibly be moved to a higher-level path manipulation package.
	//@ requires  Mem() && Valid(ub)
	//@ preserves sl.AbsSlice_Bytes(ub, 0, len(ub))
	//@ ensures   e == nil ==> p != nil
	//@ ensures   e == nil ==> p.Mem() && p.Valid(ub)
	//@ ensures   e != nil ==> e.ErrorMem()
	//@ decreases
	Reverse( /*@ ghost ub []byte @*/ ) (p Path, e error)
	// Len returns the length of a path in bytes.
	// TODO: make this impure and use LenSpec
	//@ pure
	//@ requires acc(Mem(), _) // TODO: do we need Valid?
	//@ ensures  l >= 0
	//@ decreases
	Len( /*@ ghost underlyingBuf []byte @*/ ) (l int) // TODO: drop param
	// Type returns the type of a path.
	//@ pure
	//@ requires acc(Mem(), _) // TODO: do we need Valid?
	//@ decreases
	Type( /*@ ghost underlyingBuf []byte @*/ ) Type // TODO: drop param

	// TODO: In the end, check if it is still necessary
	//@ ghost
	//@ requires Mem()
	//@ ensures  NonInitMem()
	//@ decreases
	//@ DowngradePerm(ghost underlyingBuf []byte) // TODO: drop param
}

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

// RegisterPath registers a new SCION path type globally.
// The PathType passed in must be unique, or a runtime panic will occur.
// @ requires 0 <= pathMeta.Type && pathMeta.Type < maxPathType
// @ requires PathPackageMem()
// @ requires !Registered(pathMeta.Type)
// @ requires pathMeta.New implements NewPathSpec
// @ ensures  PathPackageMem()
// @ ensures  forall t Type :: { old(Registered(t)) }{ Registered(t) } 0 <= t && t < maxPathType ==>
// @ 	t != pathMeta.Type ==> old(Registered(t)) == Registered(t)
// @ ensures  Registered(pathMeta.Type)
// @ decreases
func RegisterPath(pathMeta Metadata) {
	//@ unfold PathPackageMem()
	pm := registeredPaths[pathMeta.Type]
	if pm.inUse {
		panic("path type already registered")
	}
	registeredPaths[pathMeta.Type].inUse = true
	registeredPaths[pathMeta.Type].Metadata = pathMeta
	//@ fold PathPackageMem()
}

// StrictDecoding enables or disables strict path decoding. If enabled, unknown
// path types fail to decode. If disabled, unknown path types are decoded into a
// raw path that keeps the encoded path around for re-serialization.
//
// Strict parsing is enabled by default.
//
// Experimental: This function is experimental and might be subject to change.
// @ requires PathPackageMem()
// @ ensures  PathPackageMem()
// @ decreases
func StrictDecoding(strict bool) {
	//@ unfold PathPackageMem()
	strictDecoding = strict
	//@ fold PathPackageMem()
}

// NewPath returns a new path object of pathType.
// @ requires 0 <= pathType && pathType < maxPathType
// @ requires acc(PathPackageMem(), _)
// @ ensures  e != nil ==> e.ErrorMem()
// @ ensures  e == nil ==> p != nil && p.NonInitMem()
// @ decreases
func NewPath(pathType Type) (p Path, e error) {
	//@ unfold acc(PathPackageMem(), _)
	pm := registeredPaths[pathType]
	if !pm.inUse {
		if strictDecoding {
			return nil, serrors.New("unsupported path", "type", uint8(pathType))
		}
		tmp := &rawPath{}
		//@ fold tmp.NonInitMem()
		return tmp, nil
	}
	return pm.New() /*@ as NewPathSpec @*/, nil
}

// NewRawPath returns a new raw path that can hold any path type.
// @ ensures p != nil
// @ ensures p.NonInitMem()
// @ decreases
func NewRawPath() (p Path) {
	p = &rawPath{}
	//@ fold p.NonInitMem()
	return p
}

type rawPath struct {
	raw      []byte
	pathType Type
}

// @ preserves acc(p.Mem(), R10) && p.Valid(ub)
// @ preserves acc(sl.AbsSlice_Bytes(ub, 0, len(ub)), R10)
// @ preserves sl.AbsSlice_Bytes(b, 0, len(b))
// @ ensures   e == nil
// @ decreases
func (p *rawPath) SerializeTo(b []byte /*@, ghost ub []byte @*/) (e error) {
	//@ unfold sl.AbsSlice_Bytes(b, 0, len(b))
	//@ unfold acc(p.Mem(), R10)
	//@ unfold acc(sl.AbsSlice_Bytes(p.raw, 0, len(p.raw)), R11)
	copy(b, p.raw /*@, R11 @*/)
	//@ fold acc(sl.AbsSlice_Bytes(p.raw, 0, len(p.raw)), R11)
	//@ fold acc(p.Mem(), R10)
	//@ fold sl.AbsSlice_Bytes(b, 0, len(b))
	return nil
}

// @ requires  p.NonInitMem()
// @ preserves sl.AbsSlice_Bytes(b, 0, len(b))
// @ ensures   p.Mem() && p.Valid(b)
// @ ensures   e == nil
// @ decreases
func (p *rawPath) DecodeFromBytes(b []byte) (e error) {
	//@ unfold p.NonInitMem()
	p.raw = b
	//@ fold p.Mem()
	return nil
}

// @ ensures  e != nil && e.ErrorMem()
// @ decreases
func (p *rawPath) Reverse( /*@ ghost underlyingBuf []byte @*/ ) (r Path, e error) {
	return nil, serrors.New("not supported")
}

// @ pure
// @ requires acc(p.Mem(), _)
// @ ensures l >= 0
// @ decreases
func (p *rawPath) Len( /*@ ghost ub []byte @*/ ) (l int) {
	return /*@ unfolding acc(p.Mem(), _) in @*/ len(p.raw)
}

// @ pure
// @ requires acc(p.Mem(), _)
// @ decreases
func (p *rawPath) Type( /*@ ghost underlyingBuf []byte @*/ ) Type {
	return /*@ unfolding acc(p.Mem(), _) in @*/ p.pathType
}
