// Copyright 2017 ETH Zurich
// Copyright 2020 ETH Zurich, Anapaya Systems
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

//go:build go1.9 && linux
// +build go1.9,linux

// +gobra

// Package conn implements underlay sockets.
package conn

import (
	"net"
	"syscall"
	"time"

	"golang.org/x/net/ipv4"
	"golang.org/x/net/ipv6"

	"github.com/scionproto/scion/pkg/log"
	"github.com/scionproto/scion/pkg/private/serrors"
	"github.com/scionproto/scion/private/underlay/sockctrl"
	//@ "github.com/scionproto/scion/verification/utils/definitions"
	//@ "github.com/scionproto/scion/verification/utils/slices"
)

// Messages is a list of ipX.Messages. It is necessary to hide the type alias
// between ipv4.Message, ipv6.Message and socket.Message.
type Messages []ipv4.Message

// Conn describes the API for an underlay socket
type Conn interface {
	//@ pred Mem()
	// (VerifiedSCION) Reads a message to b. Returns the number of read bytes.
	//@ preserves Mem()
	//@ preserves slices.AbsSlice_Bytes(b, 0, len(b))
	//@ ensures   err == nil ==> 0 <= n && n <= len(b)
	//@ ensures   err == nil ==> acc(addr.Mem(), _)
	//@ ensures   err != nil ==> err.ErrorMem()
	ReadFrom(b []byte) (n int, addr *net.UDPAddr, err error)
	//@ preserves Mem()
	//@ preserves forall i int :: 0 <= i && i < len(m) ==> UnderlayConnValidMsg(&m[i])
	//@ ensures   err == nil ==> 0 <= n && n <= len(m)
	//@ ensures   err != nil ==> err.ErrorMem()
	ReadBatch(m Messages) (n int, err error)
	//@ preserves Mem()
	//@ preserves acc(slices.AbsSlice_Bytes(b, 0, len(b)), definitions.ReadL15)
	//@ ensures   err == nil ==> 0 <= n && n <= len(b)
	//@ ensures   err != nil ==> err.ErrorMem()
	Write(b []byte) (n int, err error)
	//@ requires  acc(u.Mem(), _)
	//@ preserves Mem()
	//@ preserves acc(slices.AbsSlice_Bytes(b, 0, len(b)), definitions.ReadL15)
	//@ ensures   err == nil ==> 0 <= n && n <= len(b)
	//@ ensures   err != nil ==> err.ErrorMem()
	WriteTo(b []byte, u *net.UDPAddr) (n int, err error)
	//@ requires  0 <= k && k <= len(m)
	//@ preserves Mem()
	//@ preserves forall i int :: 0 <= i && i < len(m) ==> acc(UnderlayConnValidMsg(&m[i]), definitions.ReadL15)
	//@ ensures   err == nil ==> 0 <= n && n <= k && n <= len(m)
	//@ ensures   err != nil ==> err.ErrorMem()
	WriteBatch(m Messages, k int) (n int, err error)
	//@ preserves acc(Mem(), definitions.ReadL15)
	//@ ensures   acc(u.Mem(), _)
	//@ decreases
	LocalAddr() (u *net.UDPAddr)
	//@ preserves acc(Mem(), definitions.ReadL15)
	//@ ensures   acc(u.Mem(), _)
	//@ decreases
	RemoteAddr() (u *net.UDPAddr)
	//@ preserves Mem()
	//@ ensures   err != nil ==> err.ErrorMem()
	//@ decreases
	SetReadDeadline(time.Time) (err error)
	//@ preserves Mem()
	//@ ensures   err != nil ==> err.ErrorMem()
	//@ decreases
	SetWriteDeadline(time.Time) (err error)
	//@ preserves Mem()
	//@ ensures   err != nil ==> err.ErrorMem()
	//@ decreases
	SetDeadline(time.Time) (err error)
	//@ requires Mem()
	//@ ensures  err != nil ==> err.ErrorMem()
	//@ decreases
	Close() (err error)
}

// Config customizes the behavior of an underlay socket.
type Config struct {
	// SendBufferSize is the size of the operating system send buffer, in bytes.
	// If zero, the operating system default is used.
	SendBufferSize int
	// ReceiveBufferSize is the size of the operating system receive buffer, in
	// bytes.
	ReceiveBufferSize int
}

// New opens a new underlay socket on the specified addresses.
//
// The config can be used to customize socket behavior.
//@ trusted
func New(listen, remote *net.UDPAddr, cfg *Config) (Conn, error) {
	a := listen
	if remote != nil {
		a = remote
	}
	if listen == nil && remote == nil {
		panic("either listen or remote must be set")
	}
	if a.IP.To4() != nil {
		return newConnUDPIPv4(listen, remote, cfg)
	}
	return newConnUDPIPv6(listen, remote, cfg)
}

type connUDPIPv4 struct {
	connUDPBase
	pconn *ipv4.PacketConn
}

//@ requires cfg.Mem()
//@ requires acc(listen.Mem(), _)
//@ requires acc(remote.Mem(), _)
//@ ensures  e == nil ==> res.Mem()
//@ ensures  e != nil ==> e.ErrorMem()
//@ decreases
func newConnUDPIPv4(listen, remote *net.UDPAddr, cfg *Config) (res *connUDPIPv4, e error) {
	cc := &connUDPIPv4{}
	if err := cc.initConnUDP("udp4", listen, remote, cfg); err != nil {
		return nil, err
	}
	//@ unfold cc.connUDPBase.Mem()
	cc.pconn = ipv4.NewPacketConn(cc.conn)
	//@ fold cc.connUDPBase.MemWithoutConn()
	//@ fold cc.Mem()
	return cc, nil
}

// ReadBatch reads up to len(msgs) packets, and stores them in msgs.
// It returns the number of packets read, and an error if any.
//@ preserves c.Mem()
//@ preserves forall i int :: 0 <= i && i < len(msgs) ==> UnderlayConnValidMsg(&msgs[i])
//@ ensures   errRet == nil ==> 0 <= nRet && nRet <= len(msgs)
//@ ensures   errRet != nil ==> errRet.ErrorMem()
func (c *connUDPIPv4) ReadBatch(msgs Messages) (nRet int, errRet error) {
	//@ unfold c.Mem()
	//@ invariant 0 <= i && i <= len(msgs)
	//@ invariant forall j int :: 0 <= j && j < i ==> (&msgs[j]).Mem()
	//@ invariant forall j int :: { &msgs[j].Buffers } 0 <= j && j < i ==> getLengthBuffers(&msgs[j]) == 1
	//@ invariant forall j int :: i <= j && j < len(msgs) ==> UnderlayConnValidMsg(&msgs[j])
	//@ decreases len(msgs) - i
	//@ for i := 0; i < len(msgs); i++ {
	//@ 	assert forall j int :: 0 <= j && j < i ==> (&msgs[j]).Mem()
	//@ 	assert forall j int :: { &msgs[j].Buffers } 0 <= j && j < i ==> getLengthBuffers(&msgs[j]) == 1
	//@     underlayToMem(&msgs[i])
	//@ }
	//@ assert forall j int :: { &msgs[j].Buffers } 0 <= j && j < len(msgs) ==> getLengthBuffers(&msgs[j]) == 1
	//@ assert forall j int :: 0 <= j && j < len(msgs) ==>
	//@ 	(unfolding (&msgs[j]).Mem() in len(msgs[j].Buffers) == 1)
	n, err := c.pconn.ReadBatch(msgs, syscall.MSG_WAITFORONE)
	//@ assert forall j int :: 0 <= j && j < len(msgs) ==> (&msgs[j]).Mem()
	//@ assert forall j int :: 0 <= j && j < len(msgs) ==> old(unfolding (&msgs[j]).Mem() in len(msgs[j].Buffers) == 1)
	//@ assert forall j int :: 0 <= j && j < len(msgs) ==> unfolding (&msgs[j]).Mem() in len(msgs[j].Buffers) == 1
	//@ assert forall j int :: 0 <= j && j < len(msgs) ==> getLengthBuffers(&msgs[j]) == 1
	//@ invariant 0 <= i && i <= len(msgs)
	//@ invariant forall j int :: 0 <= j && j < i ==> UnderlayConnValidMsg(&msgs[j])
	//@ invariant forall j int :: i <= j && j < len(msgs) ==> (&msgs[j]).Mem()
	//@ invariant forall j int :: { &msgs[j].Buffers } i <= j && j < len(msgs) ==> getLengthBuffers(&msgs[j]) == 1
	//@ decreases len(msgs) - i
	//@ for i := 0; i < len(msgs); i++ {
	//@     memToUnderlay(&msgs[i])
	//@ }
	//@ fold c.Mem()
	return n, err
}

//@ trusted
func (c *connUDPIPv4) WriteBatch(msgs Messages, flags int) (int, error) {
	return c.pconn.WriteBatch(msgs, flags)
}

// SetReadDeadline sets the read deadline associated with the endpoint.
//@ trusted
func (c *connUDPIPv4) SetReadDeadline(t time.Time) error {
	return c.pconn.SetReadDeadline(t)
}

//@ trusted
func (c *connUDPIPv4) SetWriteDeadline(t time.Time) error {
	return c.pconn.SetWriteDeadline(t)
}

//@ trusted
func (c *connUDPIPv4) SetDeadline(t time.Time) error {
	return c.pconn.SetDeadline(t)
}

type connUDPIPv6 struct {
	connUDPBase
	pconn *ipv6.PacketConn
}

//@ trusted
func newConnUDPIPv6(listen, remote *net.UDPAddr, cfg *Config) (*connUDPIPv6, error) {
	cc := &connUDPIPv6{}
	if err := cc.initConnUDP("udp6", listen, remote, cfg); err != nil {
		return nil, err
	}
	cc.pconn = ipv6.NewPacketConn(cc.conn)
	return cc, nil
}

// ReadBatch reads up to len(msgs) packets, and stores them in msgs.
// It returns the number of packets read, and an error if any.
//@ trusted
func (c *connUDPIPv6) ReadBatch(msgs Messages) (int, error) {
	n, err := c.pconn.ReadBatch(msgs, syscall.MSG_WAITFORONE)
	return n, err
}

//@ trusted
func (c *connUDPIPv6) WriteBatch(msgs Messages, flags int) (int, error) {
	return c.pconn.WriteBatch(msgs, flags)
}

// SetReadDeadline sets the read deadline associated with the endpoint.
//@ trusted
func (c *connUDPIPv6) SetReadDeadline(t time.Time) error {
	return c.pconn.SetReadDeadline(t)
}

//@ trusted
func (c *connUDPIPv6) SetWriteDeadline(t time.Time) error {
	return c.pconn.SetWriteDeadline(t)
}

//@ trusted
func (c *connUDPIPv6) SetDeadline(t time.Time) error {
	return c.pconn.SetDeadline(t)
}

type connUDPBase struct {
	conn   *net.UDPConn
	Listen *net.UDPAddr
	Remote *net.UDPAddr
	closed bool
}

//@ requires acc(cc)
//@ requires acc(laddr.Mem(), _)
//@ requires acc(raddr.Mem(), _)
//@ requires cfg.Mem()
//@ ensures  errRet == nil ==> cc.Mem()
//@ ensures  errRet != nil ==> errRet.ErrorMem()
//@ decreases
func (cc *connUDPBase) initConnUDP(network string, laddr, raddr *net.UDPAddr, cfg *Config) (errRet error) {
	var c *net.UDPConn
	var err error
	if laddr == nil {
		return serrors.New("listen address must be specified")
	}
	if raddr == nil {
		if c, err = net.ListenUDP(network, laddr); err != nil {
			return serrors.WrapStr("Error listening on socket", err,
				"network", network, "listen", laddr)
		}
	} else {
		if c, err = net.DialUDP(network, laddr, raddr); err != nil {
			return serrors.WrapStr("Error setting up connection", err,
				"network", network, "listen", laddr, "remote", raddr)
		}
	}

	//@ unfold cfg.Mem()
	// Set and confirm send buffer size
	if cfg.SendBufferSize != 0 {
		beforeV, err := sockctrl.GetsockoptInt(c, syscall.SOL_SOCKET, syscall.SO_SNDBUF)
		if err != nil {
			return serrors.WrapStr("Error getting SO_SNDBUF socket option (before)", err,
				"listen", laddr,
				"remote", raddr,
			)
		}
		target := cfg.SendBufferSize
		if err = c.SetWriteBuffer(target); err != nil {
			return serrors.WrapStr("Error setting send buffer size", err,
				"listen", laddr,
				"remote", raddr,
			)
		}
		after, err := sockctrl.GetsockoptInt(c, syscall.SOL_SOCKET, syscall.SO_SNDBUF)
		if err != nil {
			return serrors.WrapStr("Error getting SO_SNDBUF socket option (after)", err,
				"listen", laddr,
				"remote", raddr,
			)
		}
		if after/2 < target {
			// Note: kernel doubles value passed in SetSendBuffer, value
			// returned is the doubled value
			log.Info("Send buffer size smaller than requested",
				"expected", target,
				"actual", after/2,
				"before", beforeV/2,
			)
		}
	}

	// Set and confirm receive buffer size
	{
		beforeV, err := sockctrl.GetsockoptInt(c, syscall.SOL_SOCKET, syscall.SO_RCVBUF)
		if err != nil {
			return serrors.WrapStr("Error getting SO_RCVBUF socket option (before)", err,
				"listen", laddr,
				"remote", raddr,
			)
		}
		target := cfg.ReceiveBufferSize
		if err = c.SetReadBuffer(target); err != nil {
			return serrors.WrapStr("Error setting recv buffer size", err,
				"listen", laddr,
				"remote", raddr,
			)
		}
		after, err := sockctrl.GetsockoptInt(c, syscall.SOL_SOCKET, syscall.SO_RCVBUF)
		if err != nil {
			return serrors.WrapStr("Error getting SO_RCVBUF socket option (after)", err,
				"listen", laddr,
				"remote", raddr,
			)
		}
		if after/2 < target {
			// Note: kernel doubles value passed in SetReadBuffer, value
			// returned is the doubled value
			log.Info("Receive buffer size smaller than requested",
				"expected", target,
				"actual", after/2,
				"before", beforeV/2,
			)
		}
	}

	cc.conn = c
	cc.Listen = laddr
	cc.Remote = raddr
	//@ fold cc.Mem()
	return nil
}

//@ trusted
func (c *connUDPBase) ReadFrom(b []byte) (int, *net.UDPAddr, error) {
	return c.conn.ReadFromUDP(b)
}

//@ trusted
func (c *connUDPBase) Write(b []byte) (int, error) {
	return c.conn.Write(b)
}

//@ trusted
func (c *connUDPBase) WriteTo(b []byte, dst *net.UDPAddr) (int, error) {
	if c.Remote != nil {
		return c.conn.Write(b)
	}
	return c.conn.WriteTo(b, dst)
}

//@ trusted
func (c *connUDPBase) LocalAddr() *net.UDPAddr {
	return c.Listen
}

//@ trusted
func (c *connUDPBase) RemoteAddr() *net.UDPAddr {
	return c.Remote
}

//@ trusted
func (c *connUDPBase) Close() error {
	if c.closed {
		return nil
	}
	c.closed = true
	return c.conn.Close()
}

// NewReadMessages allocates memory for reading IPv4 Linux network stack
// messages.
//@ trusted // for performance
//@ requires 0 < n
//@ ensures  len(res) == n
//@ ensures  forall i int :: 0 <= i && i < n ==> UnderlayConnValidMsg(&res[i])
//@ decreases
func NewReadMessages(n int) (res Messages) {
	//@ requires 0 < n
	//@ ensures  len(m) == n
	//@ ensures  forall j int :: 0 <= j && j < len(m) ==> acc(&m[j])
	//@ ensures  forall j int :: { m[j].Addr } 0 <= j && j < len(m) ==> m[j].Addr == nil
	//@ ensures  forall j int :: { m[j].OOB } 0 <= j && j < len(m) ==> m[j].OOB == nil
	//@ decreases
	//@ outline(
	m := make(Messages, n)
	//@ )
	//@ assert forall j int :: 0 <= j && j < len(m) ==> m[j].Addr == nil
	//@ invariant forall j int :: (0 <= j && j < i) ==> UnderlayConnValidMsg(&m[j])
	//@ invariant forall j int :: (i <= j && j < len(m)) ==> acc(&m[j])
	//@ invariant forall j int :: { m[j].Addr } (i <= j && j < len(m)) ==> m[j].Addr == nil
	//@ invariant forall j int :: { m[j].OOB } (i <= j && j < len(m)) ==> m[j].OOB == nil
	//@ decreases len(m) - i
	for i := range m {
		// Allocate a single-element, to avoid allocations when setting the buffer.
		//@ preserves acc(&(m[i].Buffers))
		//@ ensures   len(m[i].Buffers) == 1
		//@ ensures   acc(&(m[i].Buffers[0]))
		//@ ensures   slices.AbsSlice_Bytes(m[i].Buffers[0], 0, len(m[i].Buffers[0]))
		//@ decreases
		//@ outline(
		m[i].Buffers = make([][]byte, 1)
		//@ fold slices.AbsSlice_Bytes(m[i].Buffers[0], 0, len(m[i].Buffers[0]))
		//@ )
		//@ assert acc(&m[i])
		//@ assert len(m[i].Buffers) == 1
		//@ assert acc(&m[i].Buffers[0])
		//@ assert slices.AbsSlice_Bytes(m[i].Buffers[0], 0, len(m[i].Buffers[0]))
		//@ assert m[i].Addr == nil
		//@ fold slices.AbsSlice_Bytes(m[i].OOB, 0, len(m[i].OOB))
		//@ fold UnderlayConnValidMsg(&m[i])
	}
	return m
}
