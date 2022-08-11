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

//@ trusted
//@ requires acc(s.Mem(), _)
//@ requires acc(a.Mem())
func (s *services) AddSvc(svc addr.HostSVC, a *net.UDPAddr) {
	//@ unfold acc(s.Mem(), _)
	s.mtx.Lock()
	defer s.mtx.Unlock()

	//@ unfold internalLockInv!<s!>()
	//@ ghost defer fold internalLockInv!<s!>()
	addrs := s.m[svc]
	/*@
	ghost if addrs == nil {
		fold validMapValue(addrs)
	}
	@*/
	if _, ok := s.index(a, addrs); ok {
		return
	}
	//@ unfold validMapValue(addrs)
	//@ ghost defer fold validMapValue(addrs)
	s.m[svc] = append( /*@ definitions.ReadL10, @*/ addrs, a)
}

//@ trusted
func (s *services) DelSvc(svc addr.HostSVC, a *net.UDPAddr) {
	s.mtx.Lock()
	defer s.mtx.Unlock()

	addrs := s.m[svc]
	index, ok := s.index(a, addrs)
	if !ok {
		return
	}
	addrs[index] = addrs[len(addrs)-1]
	addrs[len(addrs)-1] = nil
	s.m[svc] = addrs[:len(addrs)-1]
}

//@ trusted
func (s *services) Any(svc addr.HostSVC) (*net.UDPAddr, bool) {
	s.mtx.Lock()
	defer s.mtx.Unlock()

	addrs := s.m[svc]
	if len(addrs) == 0 {
		return nil, false
	}
	return addrs[mrand.Intn(len(addrs))], true
}

//@ preserves acc(a.Mem(), definitions.ReadL10)
//@ preserves acc(validMapValue(addrs), definitions.ReadL10)
//@ ensures   b ==> res >= 0 && 0 < len(addrs) && 0 <= res && res < len(addrs)
//@ ensures   !b ==> res == -1
// ensures   !b == unfolding acc(validMapValue(addrs), definitions.ReadL10) in
// 	(forall i int :: 0 <= i && i < len(addrs) ==> !equalUDPAddr(a, addrs[i]))
//@ decreases
func (s *services) index(a *net.UDPAddr, addrs []*net.UDPAddr) (res int, b bool) {
	//@ unfold acc(validMapValue(addrs), definitions.ReadL11)
	//@ defer  fold acc(validMapValue(addrs), definitions.ReadL11)
	//@ assert acc(addrs, definitions.ReadL11)
	//@ assert (forall i1 int :: 0 <= i1 && i1 < len(addrs) ==> (forall j int :: 0 <= j && j < len(addrs) ==> (i1 != j ==> &addrs[i1] != &addrs[j])))
	//@ assert forall i1 int :: 0 <= i1 && i1 < len(addrs) ==> acc(addrs[i1].Mem(), _)

	//@ assume len(addrs) > 0

	//@ invariant acc(a.Mem(), definitions.ReadL10)
	//@ invariant (forall i1 int :: 0 <= i1 && i1 < len(addrs) ==> (forall j int :: 0 <= j && j < len(addrs) ==> (i1 != j ==> &addrs[i1] != &addrs[j])))
	//@ invariant acc(addrs, definitions.ReadL11)
	//@ invariant (forall i1, j1 int :: /*{&addrs[i1], &addrs[j1]}*/ (0 <= i1 && i1 < len(addrs) && 0 <= j1 && j1 < len(addrs) && i1 != j1) ==>
	//@ 	(&addrs[i1] != &addrs[j1] && addrs[i1] != addrs[j1]))
	//@ invariant forall i1 int :: 0 <= i1 && i1 < len(addrs) ==> acc(addrs[i1].Mem(), _)
	// invariant forall i1, j1 int :: { &addrs[i1], &addrs[j1] } 0 <= i1 && i1 < len(addrs) ==>
	//	(0 <= j1 && j1 < len(addrs) ==>
	//	(i1 != j1 ==> !equalUDPAddr(addrs[i1], addrs[j1])))
	//@ decreases len(addrs) - i
	for i, o := range addrs {
		//@ unfold acc(a.Mem(), definitions.ReadL10)
		//@ unfold acc(o.Mem(), _)
		if a.IP.Equal(o.IP) && a.Port == o.Port {
			//@ fold acc(a.Mem(), definitions.ReadL10)
			return i, true
		}
		//@ fold acc(a.Mem(), definitions.ReadL10)
	}
	return -1, false
}
