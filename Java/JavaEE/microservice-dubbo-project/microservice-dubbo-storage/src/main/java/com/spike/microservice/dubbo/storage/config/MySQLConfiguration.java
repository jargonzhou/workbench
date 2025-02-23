package com.spike.microservice.dubbo.storage.config;

import org.springframework.context.annotation.Configuration;
import org.springframework.context.annotation.ImportResource;
import org.springframework.transaction.annotation.EnableTransactionManagement;

@Configuration
@EnableTransactionManagement
@ImportResource("classpath:spring-mysql.xml")
public class MySQLConfiguration {

}
