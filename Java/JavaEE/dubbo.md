#  Quickstart

## Test

```shell
mvn clean install -Dmaven.test.skip=true
mvn eclipse:clean eclipse:eclipse
mvn dependency:sources -DdownloadSources=true
#mvn dependency:resolve -Dclassifier=javadoc
```

- Provider: `com.spike.microservice.dubbo.business.demo.TestProvider`
- Consumer: `com.spike.microservice.dubbo.business.demo.TestConsumer`, `com.spike.microservice.dubbo.MicroserviceDubboApiStarter`

## rest protocol

REF [在Dubbo中开发REST风格的远程调用（RESTful Remoting）](https://dangdangdotcom.github.io/dubbox/rest.html)

### dubbo-provider.xml

```xml
	<!-- rest -->
	<dubbo:protocol name="rest" port="8888" server="servlet"
		contextpath="rest" />

	<!-- 声明需要暴露的服务接口 -->
	<dubbo:service interface="com.spike.microservice.dubbo.business.demo.DemoService"
		protocol="rest" ref="demoService" />
```

注意: server选择了servlet, 依托Servlet容器执行(见WebConfiguration).

### DemoService

```java
	@Path("demoService")
	@Produces({ MediaType.APPLICATION_JSON })
	public interface DemoService {
	  @GET
	  @Path("{name : \\w+}")
	  String sayHello(@PathParam("name") String name);

	  @POST
	  @Path("sayHello")
	  ApiResponse<String> sayHello(ApiRequest<String> request);
	}
```

### WebConfiguration

```java
	  // Dubbo's DispatcherServlet
	  @Bean
	  public ServletRegistrationBean<com.alibaba.dubbo.remoting.http.servlet.DispatcherServlet>
	      dubboDispatcherServlet() {
	    ServletRegistrationBean<com.alibaba.dubbo.remoting.http.servlet.DispatcherServlet> bean =
	        new ServletRegistrationBean<>(
	            new com.alibaba.dubbo.remoting.http.servlet.DispatcherServlet(), "/http/*", "/rest/*");
	    bean.setLoadOnStartup(1);
	    return bean;
	  }

	  @Bean
	  public ServletListenerRegistrationBean<com.alibaba.dubbo.remoting.http.servlet.BootstrapListener>
	      BootstrapListener() {
	    ServletListenerRegistrationBean<com.alibaba.dubbo.remoting.http.servlet.BootstrapListener> bean =
	        new ServletListenerRegistrationBean<com.alibaba.dubbo.remoting.http.servlet.BootstrapListener>(
	            new com.alibaba.dubbo.remoting.http.servlet.BootstrapListener());
	    return bean;
	  }
```

### ZK node info

```shell
ls /dubbo/com.spike.microservice.dubbo.business.demo.DemoService/providers
[rest%3A%2F%2F192.168.1.104%3A8888%2Frest%2Fcom.spike.microservice.dubbo.business.demo.DemoService%3Fanyhost%3Dtrue%26application%3Dhello-world-app%26dubbo%3D2.6.0%26generic%3Dfalse%26interface%3Dcom.spike.microservice.dubbo.business.demo.DemoService%26methods%3DsayHello%26pid%3D8064%26server%3Dservlet%26side%3Dprovider%26timestamp%3D1524753422404]

rest://192.168.1.104:8888/rest/com.spike.microservice.dubbo.business.demo.DemoService?anyhost=true&application=hello-world-app&dubbo=2.6.0&generic=false&interface=com.spike.microservice.dubbo.business.demo.DemoService&methods=sayHello&pid=8064&server=servlet&side=provider&timestamp=1524753422404
```

### Requests and Responses

request 1:

```shell
GET http://127.0.0.1:8888/rest/demoService/zhoujiagen

Hello zhoujiagen
```

request 2:

```shell
POST http://127.0.0.1:8888/rest/demoService/sayHello
body:

	{
		"data": "zhoujiagen"
	}

response:

	{
	    "time": 1524753459850,
	    "success": 1,
	    "data": "Hello zhoujagen",
	    "msg": null,
	    "request": {
	        "time": 1524753459847,
	        "data": "zhoujagen",
	        "previousResponse": null
	    }
	}
```
