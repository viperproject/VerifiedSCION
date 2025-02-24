// Code generated by MockGen. DO NOT EDIT.
// Source: github.com/scionproto/scion/private/mgmtapi/segments/api (interfaces: SegmentStore)

// Package mock_api is a generated GoMock package.
package mock_api

import (
	context "context"
	reflect "reflect"

	gomock "github.com/golang/mock/gomock"
	query "github.com/scionproto/scion/private/pathdb/query"
)

// MockSegmentStore is a mock of SegmentStore interface.
type MockSegmentStore struct {
	ctrl     *gomock.Controller
	recorder *MockSegmentStoreMockRecorder
}

// MockSegmentStoreMockRecorder is the mock recorder for MockSegmentStore.
type MockSegmentStoreMockRecorder struct {
	mock *MockSegmentStore
}

// NewMockSegmentStore creates a new mock instance.
func NewMockSegmentStore(ctrl *gomock.Controller) *MockSegmentStore {
	mock := &MockSegmentStore{ctrl: ctrl}
	mock.recorder = &MockSegmentStoreMockRecorder{mock}
	return mock
}

// EXPECT returns an object that allows the caller to indicate expected use.
func (m *MockSegmentStore) EXPECT() *MockSegmentStoreMockRecorder {
	return m.recorder
}

// DeleteSegment mocks base method.
func (m *MockSegmentStore) DeleteSegment(arg0 context.Context, arg1 string) error {
	m.ctrl.T.Helper()
	ret := m.ctrl.Call(m, "DeleteSegment", arg0, arg1)
	ret0, _ := ret[0].(error)
	return ret0
}

// DeleteSegment indicates an expected call of DeleteSegment.
func (mr *MockSegmentStoreMockRecorder) DeleteSegment(arg0, arg1 interface{}) *gomock.Call {
	mr.mock.ctrl.T.Helper()
	return mr.mock.ctrl.RecordCallWithMethodType(mr.mock, "DeleteSegment", reflect.TypeOf((*MockSegmentStore)(nil).DeleteSegment), arg0, arg1)
}

// Get mocks base method.
func (m *MockSegmentStore) Get(arg0 context.Context, arg1 *query.Params) (query.Results, error) {
	m.ctrl.T.Helper()
	ret := m.ctrl.Call(m, "Get", arg0, arg1)
	ret0, _ := ret[0].(query.Results)
	ret1, _ := ret[1].(error)
	return ret0, ret1
}

// Get indicates an expected call of Get.
func (mr *MockSegmentStoreMockRecorder) Get(arg0, arg1 interface{}) *gomock.Call {
	mr.mock.ctrl.T.Helper()
	return mr.mock.ctrl.RecordCallWithMethodType(mr.mock, "Get", reflect.TypeOf((*MockSegmentStore)(nil).Get), arg0, arg1)
}
