package handler

import (
	"encoding/json"
	"fmt"
	"log"
	"net/http"

	"crypto/sha256"

	"github.com/gorilla/mux"

	"hellogorilla/core"
)

type UserLoginRequest struct {
	Name     string `json:"name"`
	Password string `json:"password"`
}

const (
	HEADER_TOKEN_KEY = "X-AUTH-TOKEN"
)

var Tokens map[string]string

func registerUserController(router *mux.Router) {
	Tokens = make(map[string]string)

	router.Handle("/api/user/login",
		JsonResponseMiddleWare(http.HandlerFunc(Login))).Methods("POST")
}

func Login(w http.ResponseWriter, r *http.Request) {
	var user UserLoginRequest
	err := json.NewDecoder(r.Body).Decode(&user)
	if err != nil {
		HandleError(&core.ApiError{
			Request:  r,
			Response: w,
			Code:     "ERROR_INPUT",
			Message:  "参数错误",
		})
	}

	if user.Name == "admin" && user.Password == "admin" {
		hash := sha256.New()
		hash.Write([]byte(user.Password))
		hashValue := fmt.Sprintf("%x", hash.Sum(nil))
		Tokens[hashValue] = user.Name
		w.Header().Set(HEADER_TOKEN_KEY, hashValue)
		w.WriteHeader(http.StatusOK)
		response := core.SuccessApiResponse(hashValue)
		err = json.NewEncoder(w).Encode(response)
		if err != nil {
			log.Println("Write login response failed!")
		}
	} else {
		//http.Redirect(w, r, "/index.html", http.StatusForbidden)
		HandleError(&core.ApiError{
			Request:  r,
			Response: w,
			Code:     "ERROR_LOGIN",
			Message:  "登录出错",
		})
	}
}
