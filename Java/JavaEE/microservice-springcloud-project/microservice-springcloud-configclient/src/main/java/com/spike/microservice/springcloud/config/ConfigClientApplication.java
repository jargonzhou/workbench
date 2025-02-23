package com.spike.microservice.springcloud.config;

import java.util.Arrays;

import org.springframework.beans.factory.annotation.Value;
import org.springframework.boot.SpringApplication;
import org.springframework.boot.autoconfigure.SpringBootApplication;
import org.springframework.context.ConfigurableApplicationContext;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RestController;

@RestController
@SpringBootApplication
public class ConfigClientApplication {

  @Value("${spring.datasource.url}")
  private String jdbcUrl;

  @RequestMapping("/jdbcurl")
  public Object url() {
    return jdbcUrl;
  }

  public static void main(String[] args) {
    ConfigurableApplicationContext ctx = SpringApplication.run(ConfigClientApplication.class, args);

    String[] beanNames = ctx.getBeanDefinitionNames();
    Arrays.sort(beanNames);
    System.out.println("ApplicationContext Bean definitions: ");
    for (String beanName : beanNames) {
      System.out.println("|-- " + beanName);
    }

  }

}
