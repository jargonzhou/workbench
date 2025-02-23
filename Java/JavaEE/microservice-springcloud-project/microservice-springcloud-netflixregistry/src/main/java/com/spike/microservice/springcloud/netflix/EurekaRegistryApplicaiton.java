package com.spike.microservice.springcloud.netflix;

import org.springframework.boot.SpringApplication;
import org.springframework.boot.autoconfigure.SpringBootApplication;
import org.springframework.cloud.netflix.eureka.server.EnableEurekaServer;

@EnableEurekaServer
@SpringBootApplication
public class EurekaRegistryApplicaiton {

  public static void main(String[] args) {
    SpringApplication.run(EurekaRegistryApplicaiton.class, args);

    // ConfigurableApplicationContext ctx =
    // SpringApplication.run(EurekaRegistryApplicaiton.class, args);
    //
    // String[] beanNames = ctx.getBeanDefinitionNames();
    // Arrays.sort(beanNames);
    // System.out.println("ApplicationContext Bean definitions: ");
    // for (String beanName : beanNames) {
    // System.out.println("|-- " + beanName);
    // }
  }

}
