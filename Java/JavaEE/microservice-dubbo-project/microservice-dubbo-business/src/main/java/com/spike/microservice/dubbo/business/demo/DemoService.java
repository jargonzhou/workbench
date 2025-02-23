package com.spike.microservice.dubbo.business.demo;

import javax.ws.rs.GET;
import javax.ws.rs.POST;
import javax.ws.rs.Path;
import javax.ws.rs.PathParam;
import javax.ws.rs.Produces;
import javax.ws.rs.core.MediaType;

import com.spike.microservice.commons.api.ApiRequest;
import com.spike.microservice.commons.api.ApiResponse;

@Path("demoService")
// @Path("com.spike.microservice.dubbo.business.demo.DemoService") // also ok
@Produces({ MediaType.APPLICATION_JSON })
public interface DemoService {
  @GET
  @Path("{name : \\w+}")
  String sayHello(@PathParam("name") String name);

  @POST
  @Path("sayHello")
  ApiResponse<String> sayHello(ApiRequest<String> request);
}