package com.spike.microservice.dubbo.business.demo.impl;

import com.spike.microservice.commons.api.ApiRequest;
import com.spike.microservice.commons.api.ApiResponse;
import com.spike.microservice.dubbo.business.demo.DemoService;

public class DemoServiceImpl implements DemoService {
  public String sayHello(String name) {
    return "Hello " + name;
  }

  @Override
  public ApiResponse<String> sayHello(ApiRequest<String> request) {
    String requestData = request.getData();
    return new ApiResponse<String>(request, "Hello " + requestData);
  }
}