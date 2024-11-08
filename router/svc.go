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

func newServices() *services {
	return &services{m: make(map[addr.SVC][]netip.AddrPort)}
}

func (s *services) AddSvc(svc addr.SVC, a netip.AddrPort) {
	s.mtx.Lock()
	defer s.mtx.Unlock()

	//@ unfold internalLockInv!<s!>()
	addrs := s.m[svc]
	if slices.Contains(addrs, a) {
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

func (s *services) DelSvc(svc addr.SVC, a netip.AddrPort) {
	s.mtx.Lock()
	defer s.mtx.Unlock()

	//@ unfold internalLockInv!<s!>()
	addrs := s.m[svc]
	index := slices.Index(addrs, a)
	if index == -1 {
		return
	}
	//@ fold acc(hiddenPerm(a), R10)
	//@ assert 0 < len(addrs)
	//@ unfold validMapValue(svc, addrs)
	//@ unfold InjectiveMem(addrs[len(addrs)-1], len(addrs)-1)
	addrs[index] = addrs[len(addrs)-1]
	addrs[len(addrs)-1] = netip.AddrPort{}
	s.m[svc] = addrs[:len(addrs)-1]
	//@ fold validMapValue(svc, s.m[svc])
	//@ fold internalLockInv!<s!>()
	//@ fold acc(s.Mem(), R50)
}

func (s *services) Any(svc addr.SVC) (netip.AddrPort, bool) {
	s.mtx.Lock()
	defer s.mtx.Unlock()

	//@ unfold internalLockInv!<s!>()
	addrs := s.m[svc]
	if len(addrs) == 0 {
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
