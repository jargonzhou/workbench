package com.spike.microservice.dubbo.business.demo;

import org.springframework.context.support.ClassPathXmlApplicationContext;

public class TestProvider {
  public static void main(String[] args) throws Exception {

    ClassPathXmlApplicationContext context = new ClassPathXmlApplicationContext(
        new String[] { "dubbo-provider.xml", "spring-mysql.xml" });
    // context.start();
    System.in.read(); // 按任意键退出

    context.close();
  }
}
