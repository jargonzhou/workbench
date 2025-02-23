package service

import (
	"hellogorilla/domain"
	"hellogorilla/storage"
)

func AddNote(note *domain.Note) error {
	return storage.InsertNote(note)
}

func UpdateNote(note *domain.Note) error {
	return storage.UpdateNote(note)
}

func GetNotes() []domain.Note {
	return storage.SelectNotes()
}

func GetNote(id int64) (*domain.Note, error) {
	return storage.SelectNote(id)
}

func DeleteNote(id int64) error {
	return storage.DeleteNote(id)
}
