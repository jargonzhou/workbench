package com.spike.microservice.springcloud.netflix;

import org.springframework.boot.SpringApplication;
import org.springframework.boot.autoconfigure.SpringBootApplication;
import org.springframework.cloud.client.loadbalancer.LoadBalanced;
import org.springframework.context.annotation.Bean;
import org.springframework.web.client.RestTemplate;

@SpringBootApplication
public class EurekaClientApplicaiton {

  @Bean
  @LoadBalanced
  public RestTemplate restTemplate() {
    return new RestTemplate();
  }

  public static void main(String[] args) {
    SpringApplication.run(EurekaClientApplicaiton.class, args);

    // ConfigurableApplicationContext ctx = SpringApplication.run(EurekaClientApplicaiton.class,
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
