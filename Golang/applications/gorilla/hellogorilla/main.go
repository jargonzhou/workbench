package main

import (
	"log"
	"net/http"

	"github.com/gorilla/mux"
	"github.com/urfave/negroni"

	"hellogorilla/handler"
	"hellogorilla/storage"
	"hellogorilla/views"
)

var router *mux.Router

// 初始化工作: 组件编排
func init() {
	// 创建数据库连接
	storage.Open("mysql", "root:devops+mysql@tcp(127.0.0.1:3306)/movies?parseTime=true")

	// 初始化路由
	router = mux.NewRouter().StrictSlash(false)
	// 数据处理器
	handler.ResisterDataHandler(router)
	// 视图处理器
	views.RegisterViewHandler(router)
	// 静态文件
	fs := http.FileServer(http.Dir("public"))
	router.PathPrefix("/public").Handler(http.StripPrefix("/public/", fs))
	// 使用中间件
	handler.UseMiddleware(router)

	handler.DumpRouter(router)
}

func main() {
	n := negroni.New(
		negroni.NewRecovery(),
		negroni.NewLogger(),
		negroni.NewStatic(http.Dir("public")))
	n.Use(negroni.HandlerFunc(handler.AuthenticationMiddleware))
	n.UseHandler(router)

	// n.Run(":9999")

	var address = ":9999"
	server := &http.Server{
		Addr:    address,
		Handler: n,
	}
	log.Printf("Listening on %s...", address)
	server.ListenAndServe()
}
