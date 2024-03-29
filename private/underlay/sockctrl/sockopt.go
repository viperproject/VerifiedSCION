// Copyright 2017 ETH Zurich
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

package sockctrl

import (
	"net"
	"syscall"
)

//@ trusted
//@ preserves c.Mem()
//@ ensures   e != nil ==> e.ErrorMem()
//@ decreases _
func GetsockoptInt(c *net.UDPConn, level, opt int) (r int, e error) {
	var val int
	err := SockControl(c, func(fd int) error {
		var err error
		val, err = syscall.GetsockoptInt(fd, level, opt)
		return err
	})
	return val, err
}

//@ trusted
//@ preserves c.Mem()
//@ ensures   e != nil ==> e.ErrorMem()
//@ decreases _
func SetsockoptInt(c *net.UDPConn, level, opt, value int) (e error) {
	return SockControl(c, func(fd int) error {
		return syscall.SetsockoptInt(fd, level, opt, value)
	})
}
