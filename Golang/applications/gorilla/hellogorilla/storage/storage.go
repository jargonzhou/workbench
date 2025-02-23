package storage

import (
	"database/sql"
	"log"

	"time"

	_ "github.com/go-sql-driver/mysql"
)

var db *sql.DB

// 打开连接, 例: "mysql", "root:admin@tcp(127.0.0.1:3306)/movies"
func Open(driverName, dataSourceName string) {
	_db, err := sql.Open(driverName, dataSourceName)
	if err != nil {
		log.Fatalf("Open %s failed!\n", dataSourceName)
	}
	log.Printf("Open %s succeed!\n", dataSourceName)
	db = _db
	Configure(db)
}

// 配置连接
func Configure(db *sql.DB) {
	db.SetMaxOpenConns(10)
	db.SetMaxIdleConns(10)
	db.SetConnMaxLifetime(time.Minute * 5)
}

// 在事务中执行
func ExecuteInTransaction(f func() error) error {
	tx, err := db.Begin()
	if err != nil {
		log.Printf("error: %v\n", err)
		return err
	}

	err = f()
	if err != nil {
		log.Printf("error: %v\n", err)
		tx.Rollback()
		return err
	}

	tx.Commit()
	return nil
}
