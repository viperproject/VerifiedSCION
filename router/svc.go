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

//+gobra

package router

import (
	mrand "math/rand"
	"net"
	"sync"

	"github.com/scionproto/scion/pkg/addr"
	//@ "github.com/scionproto/scion/verification/utils/definitions"
)

type services struct {
	mtx sync.Mutex
	m   map[addr.HostSVC][]*net.UDPAddr
}

//@ ensures s.Mem()
//@ decreases
func newServices() (s *services) {
	tmp := &services{m: make(map[addr.HostSVC][]*net.UDPAddr)}
	//@ fold internalLockInv!<tmp!>()
	//@ ghost tmp.mtx.SetInv(internalLockInv!<tmp!>)
	//@ fold tmp.Mem()
	return tmp
}

// WIP
//@ trusted
//@ requires acc(s.Mem(), _)
//@ requires acc(a.Mem())
func (s *services) AddSvc(svc addr.HostSVC, a *net.UDPAddr) {
	//@ unfold acc(s.Mem(), _)
	s.mtx.Lock()
	defer s.mtx.Unlock()

	//@ unfold internalLockInv!<s!>()
	addrs := s.m[svc]
	/*@
	ghost if addrs == nil {
		fold validMapValue(addrs)
	}
	@*/
	//@ unfold acc(validMapValue(addrs), definitions.ReadL10)
	if _, ok := s.index(a, addrs); ok {
		//@ fold internalLockInv!<s!>()
		return
	}
	//@ unfold acc(validMapValue(addrs), definitions.ReadL10)
	s.m[svc] = append( /*@ definitions.ReadL10, @*/ addrs, a)
	//@ assert forall i, j int :: { &addrs[i], &addrs[j] } 0 <= i && i < len(addrs) ==>
	//@	(0 <= j && j < len(addrs) ==>
	//@		(i != j ==> !equalUDPAddr(addrs[i], addrs[j])))
	//@ fold validMapValue(s.m[svc])
	//@ fold internalLockInv!<s!>()
}

// WIP
//@ trusted
//@ requires  acc(s.Mem(), _)
//@ preserves acc(a.Mem(), definitions.ReadL10)
func (s *services) DelSvc(svc addr.HostSVC, a *net.UDPAddr) {
	//@ unfold acc(s.Mem(), _)
	s.mtx.Lock()
	defer s.mtx.Unlock()

	//@ unfold internalLockInv!<s!>()
	addrs := s.m[svc]
	//@ ghost if addrs == nil { fold validMapValue(addrs) }
	//@ assert validMapValue(addrs)
	index, ok := s.index(a, addrs)
	if !ok {
		//@ fold internalLockInv!<s!>()
		return
	}
	//@ assert 0 < len(addrs)
	//@ unfold validMapValue(addrs)
	addrs[index] = addrs[len(addrs)-1]
	addrs[len(addrs)-1] = nil
	//@ assert forall i int :: 0 <= i && i < len(addrs)-1 ==> &addrs[:len(addrs)-1][i] == &addrs[i]
	s.m[svc] = addrs[:len(addrs)-1]
	//@ assert forall h addr.HostSVC :: h != svc ==> s.m[h] != s.m[svc]
	//@ fold internalLockInv!<s!>()
}

// WIP
//@ requires acc(s.Mem(), _)
//@ ensures !b ==> r == nil
//@ ensures  b  ==> acc(r.Mem(), _)
func (s *services) Any(svc addr.HostSVC) (r *net.UDPAddr, b bool) {
	//@ unfold acc(s.Mem(), _)
	s.mtx.Lock()
	defer s.mtx.Unlock()

	//@ unfold internalLockInv!<s!>()
	addrs := s.m[svc]
	if len(addrs) == 0 {
		//@ fold internalLockInv!<s!>()
		return nil, false
	}
	//@ assert validMapValue(svc, addrs)
	//@ unfold acc(validMapValue(svc, addrs))
	//@ defer fold internalLockInv!<s!>()
	//@ defer fold acc(validMapValue(svc, addrs))
	return addrs[mrand.Intn(len(addrs))], true
}

// Verified but marked as trusted to improve verification time.
//@ trusted
//@ preserves acc(a.Mem(), definitions.ReadL10)
//@ preserves acc(validMapValue(k, addrs), definitions.ReadL10)
//@ ensures   b ==> res >= 0 && 0 < len(addrs) && 0 <= res && res < len(addrs)
//@ ensures   b ==> 0 < len(addrs)
//@ ensures   b ==> 0 <= res && res < len(addrs)
// The following postcondition cannot be shown to hold even though it does
// ensures   b ==> unfolding acc(validMapValue(addrs), definitions.ReadL10) in equalUDPAddr(addrs[res], a)
//@ ensures   !b ==> res == -1
//@ decreases
func (s *services) index(a *net.UDPAddr, addrs []*net.UDPAddr /*@ , ghost k addr.HostSVC @*/) (res int, b bool) {
	//@ unfold acc(validMapValue(addrs), definitions.ReadL11)
	//@ defer  fold acc(validMapValue(addrs), definitions.ReadL11)

	//@ invariant acc(a.Mem(), definitions.ReadL10)
	//@ invariant (forall i1 int :: 0 <= i1 && i1 < len(addrs) ==> (forall j int :: 0 <= j && j < len(addrs) ==> (i1 != j ==> &addrs[i1] != &addrs[j])))
	//@ invariant acc(addrs, definitions.ReadL11)
	//@ invariant forall u *net.UDPAddr :: u in sliceToSet(addrs) ==> acc(u.Mem(), _)
	//@ decreases len(addrs) - i
	for i, o := range addrs {
		// TODO: Gobra currently cannot prove that the loop is non-empty at this
		//       point, even though it must definitely not be. This assume deals
		//       with that Gobra limitation.
		//@ assume len(addrs) > 0
		//@ unfold acc(a.Mem(), definitions.ReadL10)
		//@ assert o in sliceToSet(addrs)
		//@ unfold acc(o.Mem(), _)
		if a.IP.Equal(o.IP) && a.Port == o.Port {
			//@ fold acc(a.Mem(), definitions.ReadL10)
			// The following assertion cannot be shown to hold even though it does
			// assert equalUDPAddr(addrs[i], a)
			return i, true
		}
		//@ fold acc(a.Mem(), definitions.ReadL10)
	}
	return -1, false
}
