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

package router

import (
	mrand "math/rand"
	"net"
	"sync"

	"github.com/scionproto/scion/pkg/addr"
	//@ . "github.com/scionproto/scion/verification/utils/definitions"
)

type services struct {
	mtx sync.Mutex
	m   map[addr.HostSVC][]*net.UDPAddr
}

// @ ensures s != nil && s.Mem()
// @ decreases
func newServices() (s *services) {
	tmp := &services{m: make(map[addr.HostSVC][]*net.UDPAddr)}
	//@ fold internalLockInv!<tmp!>()
	//@ ghost tmp.mtx.SetInv(internalLockInv!<tmp!>)
	//@ fold tmp.Mem()
	return tmp
}

// @ preserves acc(s.Mem(), R50)
// @ requires  acc(a.Mem(), R10)
// @ decreases 0 if sync.IgnoreBlockingForTermination()
func (s *services) AddSvc(svc addr.HostSVC, a *net.UDPAddr) {
	//@ unfold acc(s.Mem(), R50)
	s.mtx.Lock()
	defer s.mtx.Unlock()

	//@ unfold internalLockInv!<s!>()
	addrs := s.m[svc]
	//@ ghost if addrs == nil { fold validMapValue(svc, addrs) }
	//@ unfold acc(validMapValue(svc, addrs), R10)
	if _, ok := s.index(a, addrs /*@, svc @*/); ok {
		//@ fold acc(validMapValue(svc, addrs), R10)
		//@ fold internalLockInv!<s!>()
		//@ fold acc(s.Mem(), R50)
		return
	}
	//@ fold acc(validMapValue(svc, addrs), R10)
	//@ unfold validMapValue(svc, addrs)
	s.m[svc] = append( /*@ R10, @*/ addrs, a)
	//@ ghost tmp := s.m[svc]
	//@ fold InjectiveMem(tmp[len(tmp)-1], len(tmp)-1)
	//@ fold validMapValue(svc, s.m[svc])
	//@ fold internalLockInv!<s!>()
	//@ fold acc(s.Mem(), R50)
}

// @ preserves acc(s.Mem(), R50)
// @ preserves acc(a.Mem(), R10)
// @ decreases 0 if sync.IgnoreBlockingForTermination()
func (s *services) DelSvc(svc addr.HostSVC, a *net.UDPAddr) {
	//@ unfold acc(s.Mem(), R50)
	s.mtx.Lock()
	defer s.mtx.Unlock()

	//@ unfold internalLockInv!<s!>()
	addrs := s.m[svc]
	//@ ghost if addrs == nil { fold validMapValue(svc, addrs) }
	//@ assert validMapValue(svc, addrs)
	index, ok := s.index(a, addrs /*@, svc @*/)
	if !ok {
		//@ fold internalLockInv!<s!>()
		//@ fold acc(s.Mem(), R50)
		return
	}
	//@ fold acc(hiddenPerm(a), R10)
	//@ assert 0 < len(addrs)
	//@ unfold validMapValue(svc, addrs)
	//@ unfold InjectiveMem(addrs[len(addrs)-1], len(addrs)-1)
	addrs[index] = addrs[len(addrs)-1]
	//@ fold InjectiveMem(addrs[index], index)
	//@ unfold acc(hiddenPerm(a), R10)
	addrs[len(addrs)-1] = nil
	//@ assert forall i int :: { &addrs[:len(addrs)-1][i] }{ &addrs[i] } 0 <= i && i < len(addrs)-1 ==> &addrs[:len(addrs)-1][i] == &addrs[i]
	s.m[svc] = addrs[:len(addrs)-1]
	//@ fold validMapValue(svc, s.m[svc])
	//@ fold internalLockInv!<s!>()
	//@ fold acc(s.Mem(), R50)
}

// @ requires acc(s.Mem(), _)
// @ ensures  !b ==> r == nil
// @ ensures  b  ==> acc(r.Mem(), _)
// @ decreases 0 if sync.IgnoreBlockingForTermination()
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
	tmpIdx := mrand.Intn(len(addrs))
	tmpAddr := addrs[tmpIdx]
	//@ unfold InjectiveMem(tmpAddr, tmpIdx)
	//@ fold InjectiveMem(tmpAddr, tmpIdx)
	return tmpAddr, true
}

// @ preserves acc(a.Mem(), R10)
// @ preserves acc(validMapValue(k, addrs), R10)
// @ ensures   b ==> res >= 0 && 0 < len(addrs) && 0 <= res && res < len(addrs)
// @ ensures   b ==> 0 < len(addrs)
// @ ensures   b ==> 0 <= res && res < len(addrs)
// @ ensures   !b ==> res == -1
// @ decreases
func (s *services) index(a *net.UDPAddr, addrs []*net.UDPAddr /*@ , ghost k addr.HostSVC @*/) (res int, b bool) {
	// @ unfold acc(validMapValue(k, addrs), R11)
	// @ defer  fold acc(validMapValue(k, addrs), R11)

	// @ invariant acc(a.Mem(), R10)
	// @ invariant acc(addrs, R11)
	// @ invariant forall i1 int :: { addrs[i1] } 0 <= i1 && i1 < len(addrs) ==> acc(InjectiveMem(addrs[i1], i1), R11)
	// @ decreases len(addrs) - i0
	for i, o := range addrs /*@ with i0 @*/ {
		// @ unfold acc(a.Mem(), R10)
		// @ unfold acc(InjectiveMem(addrs[i], i), R11)
		// @ fold   acc(InjectiveMem(addrs[i], i), R11)
		// @ unfold acc(o.Mem(), _)
		if a.IP.Equal(o.IP) && a.Port == o.Port {
			// @ fold acc(a.Mem(), R10)
			return i, true
		}
		// @ fold acc(a.Mem(), R10)
	}
	return -1, false
}
