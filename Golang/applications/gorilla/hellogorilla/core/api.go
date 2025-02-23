package core

import (
	"net/http"
)

// 响应: 数据
type ApiResponse struct {
	Code    string
	Message string
	Data    interface{}
}

func SuccessApiResponse(data interface{}) ApiResponse {
	return ApiResponse{
		Code:    "000000",
		Message: "",
		Data:    data,
	}
}

func FailedApiResponse(code, message string) ApiResponse {
	return ApiResponse{
		Code:    code,
		Message: message,
		Data:    nil,
	}
}

// 请求错误
type ApiError struct {
	Request  *http.Request
	Response http.ResponseWriter
	Code     string
	Message  string
}

func (apiError *ApiError) ToApiResponse() ApiResponse {
	return ApiResponse{
		Code:    apiError.Code,
		Message: apiError.Message,
		Data:    nil,
	}
}
