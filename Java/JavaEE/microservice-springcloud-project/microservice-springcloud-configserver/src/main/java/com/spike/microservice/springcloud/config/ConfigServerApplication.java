package com.spike.microservice.springcloud.config;

import java.util.Arrays;

import org.springframework.boot.SpringApplication;
import org.springframework.boot.autoconfigure.SpringBootApplication;
import org.springframework.cloud.config.server.EnableConfigServer;
import org.springframework.context.ConfigurableApplicationContext;

@SpringBootApplication
@EnableConfigServer
public class ConfigServerApplication {

  public static void main(String[] args) {
    ConfigurableApplicationContext ctx = SpringApplication.run(ConfigServerApplication.class, args);

    String[] beanNames = ctx.getBeanDefinitionNames();
    Arrays.sort(beanNames);
    System.out.println("ApplicationContext Bean definitions: ");
    for (String beanName : beanNames) {
      System.out.println("|-- " + beanName);
    }
  }
}
