package handler

import (
	"log"
	"net/http"
	"strings"

	"hellogorilla/core"

	"github.com/gorilla/mux"
)

type RoutingInfo struct {
	Methods      string
	PathTemplate string

	PathRegexp       string
	QueriesTemplates string
	QueriesRegexps   string
}

var RoutingInfos []RoutingInfo

// 注册路由
func ResisterDataHandler(router *mux.Router) {
	registerApiHealth(router)
	registerNoteController(router)
	registerUserController(router)
}

func DumpRouter(r *mux.Router) {
	err := r.Walk(func(route *mux.Route, router *mux.Router, ancestors []*mux.Route) error {
		routingInfo := RoutingInfo{}
		pathTemplate, err := route.GetPathTemplate()
		if err == nil {
			routingInfo.PathTemplate = pathTemplate
		}
		pathRegexp, err := route.GetPathRegexp()
		if err == nil {
			routingInfo.PathRegexp = pathRegexp
		}
		queriesTemplates, err := route.GetQueriesTemplates()
		if err == nil {
			routingInfo.QueriesTemplates = strings.Join(queriesTemplates, ",")
		}
		queriesRegexps, err := route.GetQueriesRegexp()
		if err == nil {
			routingInfo.QueriesRegexps = strings.Join(queriesRegexps, ",")
		}
		methods, err := route.GetMethods()
		if err == nil {
			routingInfo.Methods = strings.Join(methods, ",")
		}
		log.Println(routingInfo)
		RoutingInfos = append(RoutingInfos, routingInfo)
		return nil
	})
	if err != nil {
		log.Println("Dump router failed!\n", err)
	}
}

// 使用中间件
func UseMiddleware(router *mux.Router) {
	// use negroni
	// router.Use(LoggingMiddleWare)
}

// 日志中间件
func LoggingMiddleWare(next http.Handler) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		log.Println(r.Method, r.RequestURI)

		next.ServeHTTP(w, r)
	})
}

// JSON响应中间件
func JsonResponseMiddleWare(next http.Handler) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "application/json")

		next.ServeHTTP(w, r)
	})
}

// 身份认证中间件
// TODO 增加额外的校验逻辑
func AuthenticationMiddleware(w http.ResponseWriter, r *http.Request, next http.HandlerFunc) {
	if r.URL.Path == "/api/user/login" {
		next(w, r)
	} else {
		token := r.Header.Get(HEADER_TOKEN_KEY)
		_, ok := Tokens[token]
		if !ok {
			w.WriteHeader(http.StatusNonAuthoritativeInfo)
			HandleError(&core.ApiError{
				Request:  r,
				Response: w,
				Code:     "ERROR_AUTH_INFO",
				Message:  "需要登录",
			})
		} else {
			next(w, r)
		}
	}

}
