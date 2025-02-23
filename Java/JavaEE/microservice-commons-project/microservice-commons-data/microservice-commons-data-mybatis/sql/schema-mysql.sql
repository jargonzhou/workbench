CREATE DATABASE `microservice` /*!40100 DEFAULT CHARACTER SET utf8mb4 COLLATE utf8mb4_0900_ai_ci */;

CREATE TABLE `microservice`.`users` (
  `id` BIGINT NOT NULL AUTO_INCREMENT COMMENT '主键',
  `name` VARCHAR(255) NOT NULL COMMENT '名称',
  `age` INT NULL COMMENT '年龄',
  PRIMARY KEY (`id`),
  UNIQUE INDEX `uniq_name` (`name` ASC))
ENGINE = InnoDB
DEFAULT CHARACTER SET = utf8mb4
COMMENT = '用户表';
