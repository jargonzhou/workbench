package handler

import (
	"encoding/json"
	"log"
	"net/http"

	"hellogorilla/core"
)

// 处理错误
func HandleError(apiError *core.ApiError) {
	log.Printf("ERROR: %v %v", apiError.Code, apiError.Message)
	ar := apiError.ToApiResponse()

	apiError.Response.WriteHeader(http.StatusOK)
	err := json.NewEncoder(apiError.Response).Encode(ar)
	if err != nil {
		log.Fatal("ERROR: serial response!")
	}
}
