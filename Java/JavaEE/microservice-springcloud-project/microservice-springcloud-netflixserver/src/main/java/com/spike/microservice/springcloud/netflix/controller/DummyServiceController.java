package com.spike.microservice.springcloud.netflix.controller;

import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.ResponseBody;
import org.springframework.web.bind.annotation.RestController;

@RestController
public class DummyServiceController {
  // mock a service
  @RequestMapping("/hello")
  public @ResponseBody Object hello() {
    return "hello, there. I'm " + DummyServiceController.class.getSimpleName();
  }
}
