package handler

import (
	"encoding/json"
	"log"
	"net/http"
	"strconv"

	"github.com/gorilla/mux"

	"hellogorilla/core"
	"hellogorilla/domain"
	"hellogorilla/service"
)

// note_controller
func registerNoteController(router *mux.Router) {

	router.Handle("/api/notes",
		JsonResponseMiddleWare(http.HandlerFunc(GetNotes))).Methods("GET")
	router.Handle("/api/notes",
		JsonResponseMiddleWare(http.HandlerFunc(PostNote))).Methods("POST")
	router.Handle("/api/notes/{id}",
		JsonResponseMiddleWare(http.HandlerFunc(GetNote))).Methods("GET")
	router.Handle("/api/notes/{id}",
		JsonResponseMiddleWare(http.HandlerFunc(PutNote))).Methods("PUT")
	router.Handle("/api/notes/{id}",
		JsonResponseMiddleWare(http.HandlerFunc(DeleteNote))).Methods("DELETE")
}

func PostNote(w http.ResponseWriter, r *http.Request) {
	var note domain.Note
	err := json.NewDecoder(r.Body).Decode(&note)
	if err != nil {
		HandleError(&core.ApiError{
			Request:  r,
			Response: w,
			Code:     "ERROR_INPUT",
			Message:  "参数错误",
		})
	}

	err = service.AddNote(&note)
	if err != nil {
		HandleError(&core.ApiError{
			Request:  r,
			Response: w,
			Code:     "ERROR_DB",
			Message:  err.Error(),
		})
		return
	}

	w.WriteHeader(http.StatusCreated)
	response := core.SuccessApiResponse(note.Id)
	err = json.NewEncoder(w).Encode(response)
	if err != nil {
		log.Println("Write add note response failed!")
	}
}

func PutNote(w http.ResponseWriter, r *http.Request) {
	id, err := strconv.Atoi(mux.Vars(r)["id"])
	if err != nil {
		HandleError(&core.ApiError{
			Request:  r,
			Response: w,
			Code:     "ERROR_INPUT",
			Message:  "参数错误: id",
		})
		return
	}

	var note domain.Note
	err = json.NewDecoder(r.Body).Decode(&note)
	if err != nil {
		HandleError(&core.ApiError{
			Request:  r,
			Response: w,
			Code:     "ERROR_INPUT",
			Message:  "参数错误",
		})
		return
	}
	note.Id = int64(id)

	err = service.UpdateNote(&note)
	if err != nil {
		HandleError(&core.ApiError{
			Request:  r,
			Response: w,
			Code:     "ERROR_DB",
			Message:  err.Error(),
		})
		return
	}

	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusOK)
	response := core.SuccessApiResponse(note)
	err = json.NewEncoder(w).Encode(response)
	if err != nil {
		log.Println("Write update note response failed!")
	}
}

func GetNotes(w http.ResponseWriter, r *http.Request) {
	notes := service.GetNotes()

	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusOK)
	response := core.SuccessApiResponse(notes)
	json.NewEncoder(w).Encode(response)
}

func GetNote(w http.ResponseWriter, r *http.Request) {
	id, err := strconv.Atoi(mux.Vars(r)["id"])
	note, err := service.GetNote(int64(id))
	if err != nil || note == nil {
		w.WriteHeader(http.StatusNotFound)
		response := core.FailedApiResponse(core.Code_NoteNotFound, "笔记不存在")
		json.NewEncoder(w).Encode(response)
	} else {
		w.WriteHeader(http.StatusOK)
		response := core.SuccessApiResponse(note)
		json.NewEncoder(w).Encode(response)
	}
}

func DeleteNote(w http.ResponseWriter, r *http.Request) {
	id, err := strconv.Atoi(mux.Vars(r)["id"])
	if err != nil {
		HandleError(&core.ApiError{
			Request:  r,
			Response: w,
			Code:     "ERROR_INPUT",
			Message:  "参数错误: id",
		})
		return
	}
	err = service.DeleteNote(int64(id))
	if err != nil {
		response := core.FailedApiResponse("ERROR_DB", "SQL执行出错")
		json.NewEncoder(w).Encode(response)
	} else {
		w.WriteHeader(http.StatusOK)
		response := core.SuccessApiResponse(nil)
		json.NewEncoder(w).Encode(response)
	}
}
