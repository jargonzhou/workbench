package handler

import (
	"encoding/json"
	"net/http"

	"hellogorilla/metric"

	"github.com/gorilla/mux"
)

func GetApiHealth(w http.ResponseWriter, r *http.Request) {
	json.NewEncoder(w).Encode(metric.MetricValue)
}

func registerApiHealth(router *mux.Router) {
	router.Handle("/api/health",
		JsonResponseMiddleWare(http.HandlerFunc(GetApiHealth))).Methods("GET")
}
