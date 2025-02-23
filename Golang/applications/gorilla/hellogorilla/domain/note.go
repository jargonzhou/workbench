package domain

import (
	"database/sql"
	"time"
)

/**
CREATE TABLE `Notes` (
  `id` BIGINT NOT NULL AUTO_INCREMENT COMMENT '主键',
  `title` VARCHAR(50) NOT NULL COMMENT '标题',
  `description` TEXT NULL COMMENT '内容',
  `createdAt` DATETIME NOT NULL DEFAULT CURRENT_TIMESTAMP COMMENT '创建时间',
  `updatedAt` DATETIME NOT NULL DEFAULT CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP COMMENT '修改时间',
  PRIMARY KEY (`id`))
ENGINE = InnoDB
DEFAULT CHARACTER SET = utf8mb4
COMMENT = '笔记';

ALTER TABLE `Notes`
ADD UNIQUE INDEX `uniq_title` (`title` ASC);

*/
type Note struct {
	Id          int64     `json:"id"`
	Title       string    `json:"title"`
	Description string    `json:"description"`
	CreatedAt   time.Time `json:"createdAt"`
	UpdatedAt   time.Time `json:"updatedAt"`
}

// 解析行
func (note *Note) Scan(rows *sql.Rows) error {
	// 处理NULL
	var description sql.NullString
	err := rows.Scan(&note.Id, &note.Title, &description, &note.CreatedAt, &note.UpdatedAt)
	if err != nil {
		return err
	}

	if description.Valid {
		note.Description = description.String
	}

	return nil
}
