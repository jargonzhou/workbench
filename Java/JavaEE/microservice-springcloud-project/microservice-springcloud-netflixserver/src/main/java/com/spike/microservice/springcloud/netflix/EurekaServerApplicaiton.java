package com.spike.microservice.springcloud.netflix;

import org.springframework.boot.SpringApplication;
import org.springframework.boot.autoconfigure.SpringBootApplication;

@SpringBootApplication
public class EurekaServerApplicaiton {

  public static void main(String[] args) {
    SpringApplication.run(EurekaServerApplicaiton.class, args);

    // ConfigurableApplicationContext ctx = SpringApplication.run(EurekaServerApplicaiton.class,
    // args);
    //
    // String[] beanNames = ctx.getBeanDefinitionNames();
    // Arrays.sort(beanNames);
    // System.out.println("ApplicationContext Bean definitions: ");
    // for (String beanName : beanNames) {
    // System.out.println("|-- " + beanName);
    // }
  }

}
