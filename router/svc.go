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
	"net/netip"
	"slices"
	"sync"

	"github.com/scionproto/scion/pkg/addr"
	//@ . "github.com/scionproto/scion/verification/utils/definitions"
)

type services struct {
	mtx sync.Mutex
	m   map[addr.SVC][]netip.AddrPort
}

// @ ensures s != nil && s.Mem()
// @ decreases
func newServices() (s *services) {
	tmp := &services{m: make(map[addr.SVC][]netip.AddrPort)}
	//@ fold internalLockInv!<tmp!>()
	//@ ghost tmp.mtx.SetInv(internalLockInv!<tmp!>)
	//@ fold tmp.Mem()
	return tmp
}

// @ preserves acc(s.Mem(), R50)
// @ requires  acc(a.Mem(), R10)
// @ decreases 0 if sync.IgnoreBlockingForTermination()
func (s *services) AddSvc(svc addr.SVC, a netip.AddrPort) {
	//@ unfold acc(s.Mem(), R50)
	s.mtx.Lock()
	defer s.mtx.Unlock()

	//@ unfold internalLockInv!<s!>()
	addrs := s.m[svc]
	//@ ghost if addrs == nil { fold validMapValue(svc, addrs) }
	//@ unfold acc(validMapValue(svc, addrs), R10)
	if slices.Contains(addrs, a) {
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
func (s *services) DelSvc(svc addr.SVC, a netip.AddrPort) {
	//@ unfold acc(s.Mem(), R50)
	s.mtx.Lock()
	defer s.mtx.Unlock()

	//@ unfold internalLockInv!<s!>()
	addrs := s.m[svc]
	//@ ghost if addrs == nil { fold validMapValue(svc, addrs) }
	//@ assert validMapValue(svc, addrs)
	index := slices.Index(addrs, a)
	if index == -1 {
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
	addrs[len(addrs)-1] = netip.AddrPort{}
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
func (s *services) Any(svc addr.SVC) (r netip.AddrPort, b bool) {
	//@ unfold acc(s.Mem(), _)
	s.mtx.Lock()
	defer s.mtx.Unlock()

	//@ unfold internalLockInv!<s!>()
	addrs := s.m[svc]
	if len(addrs) == 0 {
		//@ fold internalLockInv!<s!>()
		return netip.AddrPort{}, false
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
