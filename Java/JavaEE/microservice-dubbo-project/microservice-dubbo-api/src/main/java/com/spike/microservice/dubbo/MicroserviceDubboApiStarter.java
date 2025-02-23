package com.spike.microservice.dubbo;

import java.util.Arrays;

import org.springframework.boot.SpringApplication;
import org.springframework.boot.autoconfigure.SpringBootApplication;
import org.springframework.boot.autoconfigure.jdbc.DataSourceAutoConfiguration;
import org.springframework.context.ConfigurableApplicationContext;

@SpringBootApplication(exclude = { DataSourceAutoConfiguration.class })
public class MicroserviceDubboApiStarter {

  public static void main(String[] args) {
    ConfigurableApplicationContext ctx =
        SpringApplication.run(MicroserviceDubboApiStarter.class, args);

    String[] beanNames = ctx.getBeanDefinitionNames();
    Arrays.sort(beanNames);
    System.out.println("ApplicationContext Bean definitions: ");
    for (String beanName : beanNames) {
      System.out.println("|-- " + beanName);
    }
  }
}