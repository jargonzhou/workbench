CREATE TABLE `book` (
  `id` BIGINT NOT NULL AUTO_INCREMENT,
  `author` VARCHAR(255) NOT NULL,
  `isbn` VARCHAR(255) NOT NULL,
  `price` DECIMAL(8,2) NOT NULL,
  `title` VARCHAR(255) NOT NULL,
  `version` INT NOT NULL,
  PRIMARY KEY (`id`));
