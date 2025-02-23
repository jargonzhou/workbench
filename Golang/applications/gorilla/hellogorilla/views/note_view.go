package views

import (
	"html/template"
	"net/http"
	"strconv"

	"hellogorilla/domain"
	"hellogorilla/service"

	"github.com/gorilla/mux"
)

// module -> name -> template
var templates map[string]map[string]*template.Template

// 渲染模板
func RenderTemplate(
	w http.ResponseWriter,
	module string,
	name string,
	templateDefinition string,
	data interface{}) {
	tmpls, ok := templates[module]
	if !ok {
		http.Error(w, "模板模块"+module+"不存在!", http.StatusInternalServerError)
	}
	tmpl, ok := tmpls[name]
	if !ok {
		http.Error(w, "模板"+module+"/"+name+"不存在!", http.StatusInternalServerError)
	}
	err := tmpl.ExecuteTemplate(w, templateDefinition, data)
	if err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
	}
}

type EditNote struct {
	domain.Note
	Id int64
}

func initNoteView(router *mux.Router) {
	// 定义模板
	if templates == nil {
		templates = make(map[string]map[string]*template.Template)
	}

	if templates[MODULE_NOTE_TEMPLATE] == nil {
		templates[MODULE_NOTE_TEMPLATE] = make(map[string]*template.Template)
	}
	noteIndexTemplate := template.Must(
		template.ParseFiles(NOTE_TEMPLATE_PATH+"/index.html",
			NOTE_TEMPLATE_PATH+"/base.html"))
	templates[MODULE_NOTE_TEMPLATE]["index"] = noteIndexTemplate

	templates[MODULE_NOTE_TEMPLATE]["add"] = template.Must(
		template.ParseFiles(NOTE_TEMPLATE_PATH+"/add.html",
			NOTE_TEMPLATE_PATH+"/base.html"))

	templates[MODULE_NOTE_TEMPLATE]["edit"] = template.Must(
		template.ParseFiles(NOTE_TEMPLATE_PATH+"/edit.html",
			NOTE_TEMPLATE_PATH+"/base.html"))

	// 定义处理器
	router.HandleFunc("/notes",
		func(w http.ResponseWriter, r *http.Request) {
			RenderTemplate(w, MODULE_NOTE_TEMPLATE, "index", "base", service.GetNotes())
		})
	router.HandleFunc("/notes/add",
		func(w http.ResponseWriter, r *http.Request) {
			RenderTemplate(w, MODULE_NOTE_TEMPLATE, "add", "base", nil)
		})
	router.HandleFunc("/notes/save",
		func(w http.ResponseWriter, r *http.Request) {
			r.ParseForm()
			title := r.PostFormValue("title")
			description := r.PostFormValue("description")
			note := &domain.Note{Title: title, Description: description}
			err := service.AddNote(note)
			if err != nil {
				http.Error(w, "添加笔记失败: "+err.Error(), http.StatusInternalServerError)
				return
			}
			http.Redirect(w, r, "/notes", 302)
		})
	router.HandleFunc("/notes/edit/{id}",
		func(w http.ResponseWriter, r *http.Request) {
			var viewModel EditNote
			vars := mux.Vars(r)
			id, err := strconv.Atoi(vars["id"])
			if err != nil {
				http.Error(w, "id参数不存在: "+err.Error(), http.StatusBadRequest)
				return
			}
			note, err := service.GetNote(int64(id))
			if err != nil {
				http.Error(w, "笔记不存在: "+err.Error(), http.StatusBadRequest)
				return
			}
			viewModel = EditNote{Note: *note, Id: int64(id)}
			RenderTemplate(w, MODULE_NOTE_TEMPLATE, "edit", "base", viewModel)
		})
	router.HandleFunc("/notes/update/{id}",
		func(w http.ResponseWriter, r *http.Request) {
			vars := mux.Vars(r)
			id, err := strconv.Atoi(vars["id"])
			if err != nil {
				http.Error(w, "id参数不存在: "+err.Error(), http.StatusBadRequest)
				return
			}

			note, err := service.GetNote(int64(id))
			if err != nil || note == nil {
				http.Error(w, "笔记不存在: "+err.Error(), http.StatusBadRequest)
				return
			}

			r.ParseForm()
			note.Title = r.PostFormValue("title")
			note.Description = r.PostFormValue("description")
			err = service.UpdateNote(note)
			if err != nil {
				http.Error(w, "更新笔记失败: "+err.Error(), http.StatusBadRequest)
				return
			}

			http.Redirect(w, r, "/notes", 302)
		})
	router.HandleFunc("/notes/delete/{id}",
		func(w http.ResponseWriter, r *http.Request) {
			vars := mux.Vars(r)
			id, err := strconv.Atoi(vars["id"])
			if err != nil {
				http.Error(w, "id参数不存在: "+err.Error(), http.StatusBadRequest)
				return
			}
			err = service.DeleteNote(int64(id))
			if err != nil {
				http.Error(w, "删除笔记失败: "+err.Error(), http.StatusBadRequest)
				return
			}
			http.Redirect(w, r, "/notes", 302)
		})
}
