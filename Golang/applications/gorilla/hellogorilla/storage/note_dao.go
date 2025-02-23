package storage

import (
	"log"

	_ "github.com/go-sql-driver/mysql"

	"hellogorilla/domain"
)

func InsertNote(note *domain.Note) error {

	tx, err := db.Begin()
	if err != nil {
		log.Printf("error: %v\n", err)
		return err
	}

	stmt, err := db.Prepare("INSERT INTO `Notes`(`title`,`description`) VALUES (?, ?)")
	if err != nil {
		tx.Rollback()
		log.Printf("error: %v\n", err)
		return err
	}

	res, err := stmt.Exec(note.Title, note.Description)
	if err != nil {
		tx.Rollback()
		log.Printf("error: %v\n", err)
		return err
	}

	lastInsertId, err := res.LastInsertId()
	if err != nil {
		tx.Rollback()
		log.Printf("error: %v\n", err)
		return err
	}

	tx.Commit()

	// 设置ID
	note.Id = lastInsertId
	return nil
}

func SelectNotes() []domain.Note {
	rows, err := db.Query("SELECT id, title, description, createdAt, updatedAt FROM Notes")
	defer rows.Close()

	result := []domain.Note{}

	for rows.Next() {
		var note domain.Note
		err := note.Scan(rows)
		if err != nil {
			log.Printf("error: %v\n", err)
		}
		// log.Printf("%v\n", note)
		result = append(result, note)
	}

	err = rows.Err()
	if err != nil {
		log.Printf("error: %v\n", err)
	}

	return result
}

func SelectNote(id int64) (*domain.Note, error) {
	var note *domain.Note
	rows, err := db.Query("SELECT id, title, description, createdAt, updatedAt FROM Notes WHERE id = ?", id)
	defer rows.Close()

	if err != nil {
		return nil, err
	}

	for rows.Next() {
		note = &domain.Note{}
		err := note.Scan(rows)
		if err != nil {
			return nil, err
		} else {
			return note, nil
		}
	}

	return note, nil
}

func DeleteNote(id int64) error {
	return ExecuteInTransaction(func() error {
		result, err := db.Exec("DELETE FROM Notes WHERE id = ?", id)
		log.Printf("delete result = %v\n", result)
		return err
	})
}

func UpdateNote(note *domain.Note) error {
	return ExecuteInTransaction(func() error {
		result, err := db.Exec("UPDATE Notes SET title = ?, description = ? WHERE id = ?",
			note.Title, note.Description, note.Id)
		log.Printf("update result = %v\n", result)
		return err
	})
}
