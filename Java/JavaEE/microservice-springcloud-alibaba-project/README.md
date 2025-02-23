# README

## Version

- Spring Boot: 2.3.12.RELEASE
- Spring Cloud: Hoxton.SR12
- Spring Cloud Alibaba: 2.2.10-RC1
- nacos: 2.2.0
- sentinel: 1.8.6
- seata-server: 1.6.1

## mybatis-generator

MyBastic Generator usage.

## Nacos Config

- nacos

```shell title="bin/startup.sh"
#export MODE="cluster"
export MODE="standalone"
```

```shell
bin/startup.sh
```

access: http://localhost:8848/nacos/index.html (nacos/nacos)

- nacosconfig

port: 8081

resource: `GET /config/user`

## Nacos Discovery

- nacosdiscovery-provider

port: 8082

resource: `GET /echo/{message}`

- nacosdiscovery-consumer

port: 8083

resource: `GET /call/echo/{message}`, `GET /feign/echo/{message}`

## Sentinel

- sentinel-dashboard

```shell
java -Dserver.port=8849 -Dproject.name=sentinel-dashboard -jar sentinel-dashboard-1.8.6.jar
```

access: http://localhost:8849/

- nacosdiscovery-consumer

port: 8083

resource: `GET /bonjour/{name}`

## Seata

- seata-server

script: `script/server/db/mysql.sql`

```yaml title="conf/application.yml"
seata:
  config:
    # support: nacos, consul, apollo, zk, etcd3
    type: file
  registry:
    # support: nacos, eureka, redis, zk, consul, etcd3, sofa
    type: file
  store:
    # support: file 、 db 、 redis
    mode: db
    session:
      mode: db
    lock:
      mode: db
    file:
      dir: sessionStore
      max-branch-session-size: 16384
      max-global-session-size: 512
      file-write-buffer-cache-size: 16384
      session-reload-read-size: 100
      flush-disk-mode: async
    db:
      datasource: druid
      db-type: mysql
      driver-class-name: com.mysql.cj.jdbc.Driver
      url: jdbc:mysql://localhost:3306/seata?allowPublicKeyRetrieval=true&useSSL=false&serverTimezone=UTC&rewriteBatchedStatements=true
      user: root
      password: admin123
      min-conn: 10
      max-conn: 100
      global-table: global_table
      branch-table: branch_table
      lock-table: lock_table
      distributed-lock-table: distributed_lock
      query-limit: 1000
      max-wait: 5000
```

```shell
bin/seata-server.sh -p 8091 -h 127.0.0.1 -m db
```

access: http://localhost:7091/

- demo application script

```sql
CREATE DATABASE `test` /*!40100 DEFAULT CHARACTER SET utf8mb4 COLLATE utf8mb4_0900_ai_ci */ /*!80016 DEFAULT ENCRYPTION='N' */;

CREATE TABLE `undo_log` (
  `id` bigint NOT NULL AUTO_INCREMENT,
  `branch_id` bigint NOT NULL,
  `xid` varchar(100) NOT NULL,
  `context` varchar(128) NOT NULL,
  `rollback_info` longblob NOT NULL,
  `log_status` int NOT NULL,
  `log_created` datetime NOT NULL,
  `log_modified` datetime NOT NULL,
  `ext` varchar(100) DEFAULT NULL,
  PRIMARY KEY (`id`),
  UNIQUE KEY `ux_undo_log` (`xid`,`branch_id`)
) ENGINE=InnoDB AUTO_INCREMENT=1 DEFAULT CHARSET=utf8mb4;

CREATE TABLE `t_account` (
  `id` int NOT NULL AUTO_INCREMENT,
  `user_id` varchar(255) DEFAULT NULL,
  `money` int DEFAULT '0',
  PRIMARY KEY (`id`)
) ENGINE=InnoDB AUTO_INCREMENT=1 DEFAULT CHARSET=utf8mb4;


CREATE TABLE `t_storage` (
  `id` int NOT NULL AUTO_INCREMENT,
  `commodity_code` varchar(255) DEFAULT NULL,
  `count` int DEFAULT '0',
  PRIMARY KEY (`id`),
  UNIQUE KEY `commodity_code` (`commodity_code`)
) ENGINE=InnoDB AUTO_INCREMENT=1 DEFAULT CHARSET=utf8mb4;

CREATE TABLE `t_order` (
  `id` int NOT NULL AUTO_INCREMENT,
  `user_id` varchar(255) DEFAULT NULL,
  `commodity_code` varchar(255) DEFAULT NULL,
  `count` int DEFAULT '0',
  `money` int DEFAULT '0',
  PRIMARY KEY (`id`)
) ENGINE=InnoDB AUTO_INCREMENT=1 DEFAULT CHARSET=utf8mb4;

INSERT INTO `test`.`t_account`(`user_id`, `money`) VALUES ('U100001', 100);
INSERT INTO `test`.`t_storage`(`commodity_code`, `count`) VALUES ('U100001', 100);
```


- seata-business

port: 18085

resource: `GET /seata/rest`, `GET /seata/feign`

- seata-storage

port: 18082

resource: `GET /storage/{commodityCode}/{count}`

- seata-order

port: 18083

resource: `POST /order?userId=&commodityCode=&orderCount=`

- seata-account

port: 18084

resource: `POST /account?userId=&money=`


mocking failures:

```java title="AccountController.java"
	@PostMapping(value = "/account", produces = "application/json")
	public String account(String userId, int money) {
		LOGGER.info("Account Service ... xid: " + RootContext.getXID());

//		if (random.nextBoolean()) {
//			throw new RuntimeException("this is a mock Exception");
//		}
    // ...
  }
```
