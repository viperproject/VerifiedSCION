// Package api provides primitives to interact with the openapi HTTP API.
//
// Code generated by unknown module path version unknown version DO NOT EDIT.
package api

import (
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"net/url"
	"strings"

	"github.com/deepmap/oapi-codegen/pkg/runtime"
)

// RequestEditorFn  is the function signature for the RequestEditor callback function
type RequestEditorFn func(ctx context.Context, req *http.Request) error

// Doer performs HTTP requests.
//
// The standard http.Client implements this interface.
type HttpRequestDoer interface {
	Do(req *http.Request) (*http.Response, error)
}

// Client which conforms to the OpenAPI3 specification for this service.
type Client struct {
	// The endpoint of the server conforming to this interface, with scheme,
	// https://api.deepmap.com for example. This can contain a path relative
	// to the server, such as https://api.deepmap.com/dev-test, and all the
	// paths in the swagger spec will be appended to the server.
	Server string

	// Doer for performing requests, typically a *http.Client with any
	// customized settings, such as certificate chains.
	Client HttpRequestDoer

	// A list of callbacks for modifying requests which are generated before sending over
	// the network.
	RequestEditors []RequestEditorFn
}

// ClientOption allows setting custom parameters during construction
type ClientOption func(*Client) error

// Creates a new Client, with reasonable defaults
func NewClient(server string, opts ...ClientOption) (*Client, error) {
	// create a client with sane default values
	client := Client{
		Server: server,
	}
	// mutate client and add all optional params
	for _, o := range opts {
		if err := o(&client); err != nil {
			return nil, err
		}
	}
	// ensure the server URL always has a trailing slash
	if !strings.HasSuffix(client.Server, "/") {
		client.Server += "/"
	}
	// create httpClient, if not already present
	if client.Client == nil {
		client.Client = &http.Client{}
	}
	return &client, nil
}

// WithHTTPClient allows overriding the default Doer, which is
// automatically created using http.Client. This is useful for tests.
func WithHTTPClient(doer HttpRequestDoer) ClientOption {
	return func(c *Client) error {
		c.Client = doer
		return nil
	}
}

// WithRequestEditorFn allows setting up a callback function, which will be
// called right before sending the request. This can be used to mutate the request.
func WithRequestEditorFn(fn RequestEditorFn) ClientOption {
	return func(c *Client) error {
		c.RequestEditors = append(c.RequestEditors, fn)
		return nil
	}
}

// The interface specification for the client above.
type ClientInterface interface {
	// PostAuthToken request with any body
	PostAuthTokenWithBody(ctx context.Context, contentType string, body io.Reader, reqEditors ...RequestEditorFn) (*http.Response, error)

	PostAuthToken(ctx context.Context, body PostAuthTokenJSONRequestBody, reqEditors ...RequestEditorFn) (*http.Response, error)

	// GetHealthcheck request
	GetHealthcheck(ctx context.Context, reqEditors ...RequestEditorFn) (*http.Response, error)

	// PostCertificateRenewal request with any body
	PostCertificateRenewalWithBody(ctx context.Context, isdNumber int, asNumber AS, contentType string, body io.Reader, reqEditors ...RequestEditorFn) (*http.Response, error)

	PostCertificateRenewal(ctx context.Context, isdNumber int, asNumber AS, body PostCertificateRenewalJSONRequestBody, reqEditors ...RequestEditorFn) (*http.Response, error)
}

func (c *Client) PostAuthTokenWithBody(ctx context.Context, contentType string, body io.Reader, reqEditors ...RequestEditorFn) (*http.Response, error) {
	req, err := NewPostAuthTokenRequestWithBody(c.Server, contentType, body)
	if err != nil {
		return nil, err
	}
	req = req.WithContext(ctx)
	if err := c.applyEditors(ctx, req, reqEditors); err != nil {
		return nil, err
	}
	return c.Client.Do(req)
}

func (c *Client) PostAuthToken(ctx context.Context, body PostAuthTokenJSONRequestBody, reqEditors ...RequestEditorFn) (*http.Response, error) {
	req, err := NewPostAuthTokenRequest(c.Server, body)
	if err != nil {
		return nil, err
	}
	req = req.WithContext(ctx)
	if err := c.applyEditors(ctx, req, reqEditors); err != nil {
		return nil, err
	}
	return c.Client.Do(req)
}

func (c *Client) GetHealthcheck(ctx context.Context, reqEditors ...RequestEditorFn) (*http.Response, error) {
	req, err := NewGetHealthcheckRequest(c.Server)
	if err != nil {
		return nil, err
	}
	req = req.WithContext(ctx)
	if err := c.applyEditors(ctx, req, reqEditors); err != nil {
		return nil, err
	}
	return c.Client.Do(req)
}

func (c *Client) PostCertificateRenewalWithBody(ctx context.Context, isdNumber int, asNumber AS, contentType string, body io.Reader, reqEditors ...RequestEditorFn) (*http.Response, error) {
	req, err := NewPostCertificateRenewalRequestWithBody(c.Server, isdNumber, asNumber, contentType, body)
	if err != nil {
		return nil, err
	}
	req = req.WithContext(ctx)
	if err := c.applyEditors(ctx, req, reqEditors); err != nil {
		return nil, err
	}
	return c.Client.Do(req)
}

func (c *Client) PostCertificateRenewal(ctx context.Context, isdNumber int, asNumber AS, body PostCertificateRenewalJSONRequestBody, reqEditors ...RequestEditorFn) (*http.Response, error) {
	req, err := NewPostCertificateRenewalRequest(c.Server, isdNumber, asNumber, body)
	if err != nil {
		return nil, err
	}
	req = req.WithContext(ctx)
	if err := c.applyEditors(ctx, req, reqEditors); err != nil {
		return nil, err
	}
	return c.Client.Do(req)
}

// NewPostAuthTokenRequest calls the generic PostAuthToken builder with application/json body
func NewPostAuthTokenRequest(server string, body PostAuthTokenJSONRequestBody) (*http.Request, error) {
	var bodyReader io.Reader
	buf, err := json.Marshal(body)
	if err != nil {
		return nil, err
	}
	bodyReader = bytes.NewReader(buf)
	return NewPostAuthTokenRequestWithBody(server, "application/json", bodyReader)
}

// NewPostAuthTokenRequestWithBody generates requests for PostAuthToken with any type of body
func NewPostAuthTokenRequestWithBody(server string, contentType string, body io.Reader) (*http.Request, error) {
	var err error

	serverURL, err := url.Parse(server)
	if err != nil {
		return nil, err
	}

	operationPath := fmt.Sprintf("/auth/token")
	if operationPath[0] == '/' {
		operationPath = "." + operationPath
	}

	queryURL, err := serverURL.Parse(operationPath)
	if err != nil {
		return nil, err
	}

	req, err := http.NewRequest("POST", queryURL.String(), body)
	if err != nil {
		return nil, err
	}

	req.Header.Add("Content-Type", contentType)

	return req, nil
}

// NewGetHealthcheckRequest generates requests for GetHealthcheck
func NewGetHealthcheckRequest(server string) (*http.Request, error) {
	var err error

	serverURL, err := url.Parse(server)
	if err != nil {
		return nil, err
	}

	operationPath := fmt.Sprintf("/healthcheck")
	if operationPath[0] == '/' {
		operationPath = "." + operationPath
	}

	queryURL, err := serverURL.Parse(operationPath)
	if err != nil {
		return nil, err
	}

	req, err := http.NewRequest("GET", queryURL.String(), nil)
	if err != nil {
		return nil, err
	}

	return req, nil
}

// NewPostCertificateRenewalRequest calls the generic PostCertificateRenewal builder with application/json body
func NewPostCertificateRenewalRequest(server string, isdNumber int, asNumber AS, body PostCertificateRenewalJSONRequestBody) (*http.Request, error) {
	var bodyReader io.Reader
	buf, err := json.Marshal(body)
	if err != nil {
		return nil, err
	}
	bodyReader = bytes.NewReader(buf)
	return NewPostCertificateRenewalRequestWithBody(server, isdNumber, asNumber, "application/json", bodyReader)
}

// NewPostCertificateRenewalRequestWithBody generates requests for PostCertificateRenewal with any type of body
func NewPostCertificateRenewalRequestWithBody(server string, isdNumber int, asNumber AS, contentType string, body io.Reader) (*http.Request, error) {
	var err error

	var pathParam0 string

	pathParam0, err = runtime.StyleParamWithLocation("simple", false, "isd-number", runtime.ParamLocationPath, isdNumber)
	if err != nil {
		return nil, err
	}

	var pathParam1 string

	pathParam1, err = runtime.StyleParamWithLocation("simple", false, "as-number", runtime.ParamLocationPath, asNumber)
	if err != nil {
		return nil, err
	}

	serverURL, err := url.Parse(server)
	if err != nil {
		return nil, err
	}

	operationPath := fmt.Sprintf("/ra/isds/%s/ases/%s/certificates/renewal", pathParam0, pathParam1)
	if operationPath[0] == '/' {
		operationPath = "." + operationPath
	}

	queryURL, err := serverURL.Parse(operationPath)
	if err != nil {
		return nil, err
	}

	req, err := http.NewRequest("POST", queryURL.String(), body)
	if err != nil {
		return nil, err
	}

	req.Header.Add("Content-Type", contentType)

	return req, nil
}

func (c *Client) applyEditors(ctx context.Context, req *http.Request, additionalEditors []RequestEditorFn) error {
	for _, r := range c.RequestEditors {
		if err := r(ctx, req); err != nil {
			return err
		}
	}
	for _, r := range additionalEditors {
		if err := r(ctx, req); err != nil {
			return err
		}
	}
	return nil
}

// ClientWithResponses builds on ClientInterface to offer response payloads
type ClientWithResponses struct {
	ClientInterface
}

// NewClientWithResponses creates a new ClientWithResponses, which wraps
// Client with return type handling
func NewClientWithResponses(server string, opts ...ClientOption) (*ClientWithResponses, error) {
	client, err := NewClient(server, opts...)
	if err != nil {
		return nil, err
	}
	return &ClientWithResponses{client}, nil
}

// WithBaseURL overrides the baseURL.
func WithBaseURL(baseURL string) ClientOption {
	return func(c *Client) error {
		newBaseURL, err := url.Parse(baseURL)
		if err != nil {
			return err
		}
		c.Server = newBaseURL.String()
		return nil
	}
}

// ClientWithResponsesInterface is the interface specification for the client with responses above.
type ClientWithResponsesInterface interface {
	// PostAuthToken request with any body
	PostAuthTokenWithBodyWithResponse(ctx context.Context, contentType string, body io.Reader, reqEditors ...RequestEditorFn) (*PostAuthTokenResponse, error)

	PostAuthTokenWithResponse(ctx context.Context, body PostAuthTokenJSONRequestBody, reqEditors ...RequestEditorFn) (*PostAuthTokenResponse, error)

	// GetHealthcheck request
	GetHealthcheckWithResponse(ctx context.Context, reqEditors ...RequestEditorFn) (*GetHealthcheckResponse, error)

	// PostCertificateRenewal request with any body
	PostCertificateRenewalWithBodyWithResponse(ctx context.Context, isdNumber int, asNumber AS, contentType string, body io.Reader, reqEditors ...RequestEditorFn) (*PostCertificateRenewalResponse, error)

	PostCertificateRenewalWithResponse(ctx context.Context, isdNumber int, asNumber AS, body PostCertificateRenewalJSONRequestBody, reqEditors ...RequestEditorFn) (*PostCertificateRenewalResponse, error)
}

type PostAuthTokenResponse struct {
	Body         []byte
	HTTPResponse *http.Response
	JSON200      *AccessToken
	JSON400      *Problem
	JSON401      *Problem
	JSON500      *Problem
	JSON503      *Problem
}

// Status returns HTTPResponse.Status
func (r PostAuthTokenResponse) Status() string {
	if r.HTTPResponse != nil {
		return r.HTTPResponse.Status
	}
	return http.StatusText(0)
}

// StatusCode returns HTTPResponse.StatusCode
func (r PostAuthTokenResponse) StatusCode() int {
	if r.HTTPResponse != nil {
		return r.HTTPResponse.StatusCode
	}
	return 0
}

type GetHealthcheckResponse struct {
	Body         []byte
	HTTPResponse *http.Response
	JSON200      *HealthCheckStatus
	JSON500      *Problem
	JSON503      *Problem
}

// Status returns HTTPResponse.Status
func (r GetHealthcheckResponse) Status() string {
	if r.HTTPResponse != nil {
		return r.HTTPResponse.Status
	}
	return http.StatusText(0)
}

// StatusCode returns HTTPResponse.StatusCode
func (r GetHealthcheckResponse) StatusCode() int {
	if r.HTTPResponse != nil {
		return r.HTTPResponse.StatusCode
	}
	return 0
}

type PostCertificateRenewalResponse struct {
	Body         []byte
	HTTPResponse *http.Response
	JSON200      *RenewalResponse
	JSON400      *Problem
	JSON401      *Problem
	JSON404      *Problem
	JSON500      *Problem
	JSON503      *Problem
}

// Status returns HTTPResponse.Status
func (r PostCertificateRenewalResponse) Status() string {
	if r.HTTPResponse != nil {
		return r.HTTPResponse.Status
	}
	return http.StatusText(0)
}

// StatusCode returns HTTPResponse.StatusCode
func (r PostCertificateRenewalResponse) StatusCode() int {
	if r.HTTPResponse != nil {
		return r.HTTPResponse.StatusCode
	}
	return 0
}

// PostAuthTokenWithBodyWithResponse request with arbitrary body returning *PostAuthTokenResponse
func (c *ClientWithResponses) PostAuthTokenWithBodyWithResponse(ctx context.Context, contentType string, body io.Reader, reqEditors ...RequestEditorFn) (*PostAuthTokenResponse, error) {
	rsp, err := c.PostAuthTokenWithBody(ctx, contentType, body, reqEditors...)
	if err != nil {
		return nil, err
	}
	return ParsePostAuthTokenResponse(rsp)
}

func (c *ClientWithResponses) PostAuthTokenWithResponse(ctx context.Context, body PostAuthTokenJSONRequestBody, reqEditors ...RequestEditorFn) (*PostAuthTokenResponse, error) {
	rsp, err := c.PostAuthToken(ctx, body, reqEditors...)
	if err != nil {
		return nil, err
	}
	return ParsePostAuthTokenResponse(rsp)
}

// GetHealthcheckWithResponse request returning *GetHealthcheckResponse
func (c *ClientWithResponses) GetHealthcheckWithResponse(ctx context.Context, reqEditors ...RequestEditorFn) (*GetHealthcheckResponse, error) {
	rsp, err := c.GetHealthcheck(ctx, reqEditors...)
	if err != nil {
		return nil, err
	}
	return ParseGetHealthcheckResponse(rsp)
}

// PostCertificateRenewalWithBodyWithResponse request with arbitrary body returning *PostCertificateRenewalResponse
func (c *ClientWithResponses) PostCertificateRenewalWithBodyWithResponse(ctx context.Context, isdNumber int, asNumber AS, contentType string, body io.Reader, reqEditors ...RequestEditorFn) (*PostCertificateRenewalResponse, error) {
	rsp, err := c.PostCertificateRenewalWithBody(ctx, isdNumber, asNumber, contentType, body, reqEditors...)
	if err != nil {
		return nil, err
	}
	return ParsePostCertificateRenewalResponse(rsp)
}

func (c *ClientWithResponses) PostCertificateRenewalWithResponse(ctx context.Context, isdNumber int, asNumber AS, body PostCertificateRenewalJSONRequestBody, reqEditors ...RequestEditorFn) (*PostCertificateRenewalResponse, error) {
	rsp, err := c.PostCertificateRenewal(ctx, isdNumber, asNumber, body, reqEditors...)
	if err != nil {
		return nil, err
	}
	return ParsePostCertificateRenewalResponse(rsp)
}

// ParsePostAuthTokenResponse parses an HTTP response from a PostAuthTokenWithResponse call
func ParsePostAuthTokenResponse(rsp *http.Response) (*PostAuthTokenResponse, error) {
	bodyBytes, err := io.ReadAll(rsp.Body)
	defer func() { _ = rsp.Body.Close() }()
	if err != nil {
		return nil, err
	}

	response := &PostAuthTokenResponse{
		Body:         bodyBytes,
		HTTPResponse: rsp,
	}

	switch {
	case strings.Contains(rsp.Header.Get("Content-Type"), "json") && rsp.StatusCode == 200:
		var dest AccessToken
		if err := json.Unmarshal(bodyBytes, &dest); err != nil {
			return nil, err
		}
		response.JSON200 = &dest

	case strings.Contains(rsp.Header.Get("Content-Type"), "json") && rsp.StatusCode == 400:
		var dest Problem
		if err := json.Unmarshal(bodyBytes, &dest); err != nil {
			return nil, err
		}
		response.JSON400 = &dest

	case strings.Contains(rsp.Header.Get("Content-Type"), "json") && rsp.StatusCode == 401:
		var dest Problem
		if err := json.Unmarshal(bodyBytes, &dest); err != nil {
			return nil, err
		}
		response.JSON401 = &dest

	case strings.Contains(rsp.Header.Get("Content-Type"), "json") && rsp.StatusCode == 500:
		var dest Problem
		if err := json.Unmarshal(bodyBytes, &dest); err != nil {
			return nil, err
		}
		response.JSON500 = &dest

	case strings.Contains(rsp.Header.Get("Content-Type"), "json") && rsp.StatusCode == 503:
		var dest Problem
		if err := json.Unmarshal(bodyBytes, &dest); err != nil {
			return nil, err
		}
		response.JSON503 = &dest

	}

	return response, nil
}

// ParseGetHealthcheckResponse parses an HTTP response from a GetHealthcheckWithResponse call
func ParseGetHealthcheckResponse(rsp *http.Response) (*GetHealthcheckResponse, error) {
	bodyBytes, err := io.ReadAll(rsp.Body)
	defer func() { _ = rsp.Body.Close() }()
	if err != nil {
		return nil, err
	}

	response := &GetHealthcheckResponse{
		Body:         bodyBytes,
		HTTPResponse: rsp,
	}

	switch {
	case strings.Contains(rsp.Header.Get("Content-Type"), "json") && rsp.StatusCode == 200:
		var dest HealthCheckStatus
		if err := json.Unmarshal(bodyBytes, &dest); err != nil {
			return nil, err
		}
		response.JSON200 = &dest

	case strings.Contains(rsp.Header.Get("Content-Type"), "json") && rsp.StatusCode == 500:
		var dest Problem
		if err := json.Unmarshal(bodyBytes, &dest); err != nil {
			return nil, err
		}
		response.JSON500 = &dest

	case strings.Contains(rsp.Header.Get("Content-Type"), "json") && rsp.StatusCode == 503:
		var dest Problem
		if err := json.Unmarshal(bodyBytes, &dest); err != nil {
			return nil, err
		}
		response.JSON503 = &dest

	}

	return response, nil
}

// ParsePostCertificateRenewalResponse parses an HTTP response from a PostCertificateRenewalWithResponse call
func ParsePostCertificateRenewalResponse(rsp *http.Response) (*PostCertificateRenewalResponse, error) {
	bodyBytes, err := io.ReadAll(rsp.Body)
	defer func() { _ = rsp.Body.Close() }()
	if err != nil {
		return nil, err
	}

	response := &PostCertificateRenewalResponse{
		Body:         bodyBytes,
		HTTPResponse: rsp,
	}

	switch {
	case strings.Contains(rsp.Header.Get("Content-Type"), "json") && rsp.StatusCode == 200:
		var dest RenewalResponse
		if err := json.Unmarshal(bodyBytes, &dest); err != nil {
			return nil, err
		}
		response.JSON200 = &dest

	case strings.Contains(rsp.Header.Get("Content-Type"), "json") && rsp.StatusCode == 400:
		var dest Problem
		if err := json.Unmarshal(bodyBytes, &dest); err != nil {
			return nil, err
		}
		response.JSON400 = &dest

	case strings.Contains(rsp.Header.Get("Content-Type"), "json") && rsp.StatusCode == 401:
		var dest Problem
		if err := json.Unmarshal(bodyBytes, &dest); err != nil {
			return nil, err
		}
		response.JSON401 = &dest

	case strings.Contains(rsp.Header.Get("Content-Type"), "json") && rsp.StatusCode == 404:
		var dest Problem
		if err := json.Unmarshal(bodyBytes, &dest); err != nil {
			return nil, err
		}
		response.JSON404 = &dest

	case strings.Contains(rsp.Header.Get("Content-Type"), "json") && rsp.StatusCode == 500:
		var dest Problem
		if err := json.Unmarshal(bodyBytes, &dest); err != nil {
			return nil, err
		}
		response.JSON500 = &dest

	case strings.Contains(rsp.Header.Get("Content-Type"), "json") && rsp.StatusCode == 503:
		var dest Problem
		if err := json.Unmarshal(bodyBytes, &dest); err != nil {
			return nil, err
		}
		response.JSON503 = &dest

	}

	return response, nil
}
