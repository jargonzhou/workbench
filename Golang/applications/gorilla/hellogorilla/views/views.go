package views

import (
	"html/template"
	"net/http"

	"hellogorilla/handler"

	"hellogorilla/core"

	"github.com/gorilla/mux"
)

const (
	TEMPLATE_BASE = core.TEMPLATE_BASE_PATH

	MODULE_NOTE_TEMPLATE = "/note"
	NOTE_TEMPLATE_PATH   = TEMPLATE_BASE + MODULE_NOTE_TEMPLATE
)

var template404 *template.Template

// 注册视图
func RegisterViewHandler(router *mux.Router) {
	initNoteView(router)

	initNotFoundViewHandler(router)
}

// 初始化404视图.
func initNotFoundViewHandler(router *mux.Router) {
	template404 = template.Must(template.ParseFiles(core.TEMPLATE_BASE_PATH + "/404.html"))
	router.NotFoundHandler = http.HandlerFunc(HandleNotFound)
}

// 404处理器
func HandleNotFound(w http.ResponseWriter, r *http.Request) {
	w.WriteHeader(404)
	data := handler.RoutingInfos
	err := template404.ExecuteTemplate(w, "base", data)
	if err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
	}
}
