### Spring Cloud Netflix

- 2.0.x: https://cloud.spring.io/spring-cloud-netflix/2.0.x/multi/multi_spring-cloud-netflix.html

```
  1. Service Discovery: Eureka Clients
  2. Service Discovery: Eureka Server
  3. Circuit Breaker: Hystrix Clients
  4. Circuit Breaker: Hystrix Dashboard
  5. Hystrix Timeouts And Ribbon Clients
  6. Client Side Load Balancer: Ribbon
  7. Declarative REST Client: Feign
  8. External Configuration: Archaius
  9. Router and Filter: Zuul
  10. Polyglot support with Sidecar
  11. Metrics: Spectator, Servo, and Atlas
  12. HTTP Clients
```

- 4.0.1: https://docs.spring.io/spring-cloud-netflix/docs/current/reference/html/

Netflix OSS
https://netflix.github.io/

Spring Cloud Tutorial
https://www.baeldung.com/spring-cloud-series

A Guide to Spring Cloud Netflix – Hystrix
https://www.baeldung.com/?s=Spring+Cloud+Netflix

Introduction to Spring Cloud Netflix – Eureka
Learn how to register a service and make it discoverable using Eureka

A Guide to Spring Cloud Netflix – Hystrix
The article shows how to set up a fallback in application logic using Spring Cloud Hystrix.

Introduction to Spring Cloud Rest Client with Netflix Ribbon
An introduction to Spring Cloud Rest Client with Netflix Ribbon with examples of load-balancing and failure resiliency of an enhanced RestTemplate with Ribbon.

Introduction to Spring Cloud OpenFeign
Feign makes writing web service clients easier with pluggable annotation support, which includes Feign annotations and JAX-RS annotations.

#### Eureka

https://www.baeldung.com/spring-cloud-netflix-eureka

*Client-side service discovery* allows services to find and communicate with each other without hard-coding the hostname and port. 

With Netflix Eureka, each client can simultaneously act as a server to *replicate* its status to a connected peer. In other words, a client retrieves a list of all connected peers in a *service registry*, and makes all further requests to other services through a *load-balancing* algorithm.

three microservices:

- 1.a service registry (Eureka Server)

spring-cloud-starter-netflix-eureka-server

```java
@SpringBootApplication
@EnableEurekaServer
public class EurekaServerApplication
```

```yaml
server:
  port: 8761
eureka:
  client:
    registerWithEureka: false
    fetchRegistry: false
```

`registerWithEureka`: If we set this property as true, then while the server starts, the inbuilt client will try to register itself with the Eureka server.
`fetchRegistry`: If we configure this property as true, the inbuilt client will try to fetch the Eureka registry.
when we start up the Eureka *server*, we don't want to register the inbuilt client to configure itself with the server.

- 2.a REST service, which registers itself at the registry (Eureka Client)

spring-cloud-starter-netflix-eureka-client

```java
GreetingController
  @RequestMapping("/greeting")
  String greeting();
```

```yaml
spring:
  application:
    name: spring-cloud-eureka-client
server:
  port: 0
eureka:
  client:
    serviceUrl:
      defaultZone: ${EUREKA_URI:http://localhost:8761/eureka}
  instance:
    preferIpAddress: true
```

- 3.a web application, which is consuming the REST service as a registry-aware client (Spring Cloud Netflix Feign Client)

Think of Feign as a discovery-aware Spring RestTemplate using interfaces to communicate with endpoints. These interfaces will be automatically implemented at runtime, and instead of service-urls, it's using *service-names*.

spring-cloud-starter-feign
spring-cloud-starter-netflix-eureka-client

```java
@FeignClient("spring-cloud-eureka-client")
public interface GreetingClient {
    @RequestMapping("/greeting")
    String greeting();
}

@SpringBootApplication
@EnableFeignClients
@Controller
public class FeignClientApplication
```

```yaml
spring:
  application:
    name: spring-cloud-eureka-feign-client
server:
  port: 8080
eureka:
  client:
    serviceUrl:
      defaultZone: ${EUREKA_URI:http://localhost:8761/eureka}
```

#### Ribbon

https://www.baeldung.com/spring-cloud-rest-client-with-netflix-ribbon
https://www.baeldung.com/spring-cloud-netflix-ribbon-retry

Netflix Ribbon is an Inter Process Communication (IPC) cloud library. Ribbon primarily provides *client-side load balancing algorithms*.

Apart from the client-side load balancing algorithms, Ribbon provides also other features:

- *Service Discovery Integration* – Ribbon load balancers provide service discovery in dynamic environments like a cloud. Integration with Eureka and Netflix service discovery component is included in the ribbon library
- *Fault Tolerance* – the Ribbon API can dynamically determine whether the servers are up and running in a live environment and can detect those servers that are down
- *Configurable load-balancing rules* – Ribbon supports `RoundRobinRule`, `AvailabilityFilteringRule`, `WeightedResponseTimeRule` out of the box and also supports defining custom rules

spring-cloud-starter-netflix-ribbon

Ribbon API enables us to configure the following components of the load balancer:

- *Rule* – Logic component which specifies the load balancing rule we are using in our application
- *Ping* – A Component which specifies the mechanism we use to determine the server's availability in real-time
- *ServerList* – can be dynamic or static.

```java
public class RibbonConfiguration {

    @Autowired
    IClientConfig ribbonClientConfig;

    @Bean
    public IPing ribbonPing(IClientConfig config) {
        return new PingUrl();
    }

    @Bean
    public IRule ribbonRule(IClientConfig config) {
        return new WeightedResponseTimeRule();
    }
}
```

```yaml
spring:
  application:
    name: spring-cloud-ribbon

server:
  port: 8888

ping-server:
  ribbon:
    eureka:
      enabled: false
    listOfServers: localhost:9092,localhost:9999
    ServerListRefreshInterval: 15000
```

```java
@SpringBootApplication
@RestController
@RibbonClient(
  name = "ping-a-server",
  configuration = RibbonConfiguration.class)
public class ServerLocationApp

    @Autowired
    RestTemplate restTemplate;

@Configuration
public class RestTemplateConfiguration{
    @LoadBalanced
    @Bean
    RestTemplate getRestTemplate() {
        return new RestTemplate();
    }
}
```

Ribbon API can determine the server's availability through the *constant pinging* of servers at regular intervals and has a capability of skipping the servers which are not live.
In addition to that, it also implements *Circuit Breaker pattern* to filter out the servers based on specified criteria.

Retry:

```yaml
weather-service:
  ribbon:
    MaxAutoRetries: 3
    MaxAutoRetriesNextServer: 1
    retryableStatusCodes: 503, 408
    OkToRetryOnAllOperations: true
```

`MaxAutoRetries` –  the number of times a failed request is retried on the same server (default 0)
`MaxAutoRetriesNextServer` – the number of servers to try excluding the first one (default 0)
`retryableStatusCodes` – the list of HTTP status codes to retry
`OkToRetryOnAllOperations` – when this property is set to true, all types of HTTP requests are retried, not just GET ones (default)

`spring-retry`
Spring Cloud Ribbon uses Spring Retry‘s `NoBackOffPolicy` object which does nothing.

```java
@Component
private class CustomRibbonLoadBalancedRetryFactory 
  extends RibbonLoadBalancedRetryFactory {

    public CustomRibbonLoadBalancedRetryFactory(
      SpringClientFactory clientFactory) {
        super(clientFactory);
    }

    @Override
    public BackOffPolicy createBackOffPolicy(String service) {
        FixedBackOffPolicy fixedBackOffPolicy = new FixedBackOffPolicy();
        fixedBackOffPolicy.setBackOffPeriod(2000);
        return fixedBackOffPolicy;
    }
}

  @Override
  public BackOffPolicy createBackOffPolicy(String service) {
      ExponentialBackOffPolicy exponentialBackOffPolicy = 
        new ExponentialBackOffPolicy();
      exponentialBackOffPolicy.setInitialInterval(1000);
      exponentialBackOffPolicy.setMultiplier(2); 
      exponentialBackOffPolicy.setMaxInterval(10000);
      return exponentialBackOffPolicy;
  }
```

Spring Cloud Ribbon中的 7 种负载均衡策略! https://zhuanlan.zhihu.com/p/480491348
Ribbon的负载均衡策略、原理和扩展: https://www.jianshu.com/p/79b9cf0d0519

1.*轮询策略*：RoundRobinRule，按照一定的顺序依次调用服务实例。比如一共有 3 个服务，第一次调用服务 1，第二次调用服务 2，第三次调用服务3，依次类推。
2.*权重策略*：WeightedResponseTimeRule，根据每个服务提供者的*响应时间*分配一个权重，响应时间越长，权重越小，被选中的可能性也就越低。 它的实现原理是，刚开始使用轮询策略并开启一个计时器，每一段时间收集一次所有服务提供者的平均响应时间，然后再给每个服务提供者附上一个权重，权重越高被选中的概率也越大。
3.*随机策略*：RandomRule，从服务提供者的列表中随机选择一个服务实例。
4.*最小连接数策略*：BestAvailableRule，也叫最小并发数策略，它是遍历服务提供者列表，选取连接数最小的⼀个服务实例。如果有相同的最小连接数，那么会调用轮询策略进行选取。 
5.*重试策略*：RetryRule，按照*轮询策略*来获取服务，如果获取的服务实例为 null 或已经失效，则在指定的时间之内不断地进行重试来获取服务，如果超过指定时间依然没获取到服务实例则返回 null。 
6.*可用敏感性策略*：AvailabilityFilteringRule，先过滤掉*非健康*的服务实例，然后再选择*连接数较小*的服务实例。
7.*区域敏感策略*：ZoneAvoidanceRule，根据*服务所在区域（zone）*的性能和服务的可用性来选择服务实例，在没有区域的环境下，该策略和轮询策略类似。

#### Hystrix

https://github.com/Netflix/Hystrix/wiki/How-To-Use

https://www.baeldung.com/introduction-to-hystrix

The Hystrix framework library helps to control the interaction between services by providing *fault tolerance* and *latency tolerance*. 
It improves overall resilience of the system by *isolating the failing services* and *stopping the cascading effect of failures*.

```xml
  <groupId>com.netflix.hystrix</groupId>
  <artifactId>hystrix-core</artifactId>
```

The way Hystrix provides fault and latency tolerance is to *isolate and wrap calls to remote services*.

```java
class RemoteServiceTestCommand extends HystrixCommand<String> {

    private RemoteServiceTestSimulator remoteService;

    RemoteServiceTestCommand(Setter config, RemoteServiceTestSimulator remoteService) {
        super(config);
        this.remoteService = remoteService;
    }

    @Override
    protected String run() throws Exception {
        return remoteService.execute();
    }
}
```

Defensive Programming With *Timeout*:
It is general programming practice to set timeouts for calls to remote services.

```java
@Test(expected = HystrixRuntimeException.class)
public void givenSvcTimeoutOf15000AndExecTimeoutOf5000_whenRemoteSvcExecuted_thenExpectHre()
  throws InterruptedException {

    HystrixCommand.Setter config = HystrixCommand
      .Setter
      .withGroupKey(HystrixCommandGroupKey.Factory.asKey("RemoteServiceGroupTest5"));

    HystrixCommandProperties.Setter commandProperties = HystrixCommandProperties.Setter();
    commandProperties.withExecutionTimeoutInMilliseconds(5_000); // execution timeout
    config.andCommandPropertiesDefaults(commandProperties);

    new RemoteServiceTestCommand(config, new RemoteServiceTestSimulator(15_000)).execute();
}
```

Defensive Programming With *Limited Thread Pool*:
When a remote service starts to respond slowly, a typical application will continue to call that remote service.

```java
@Test
public void givenSvcTimeoutOf500AndExecTimeoutOf10000AndThreadPool_whenRemoteSvcExecuted
  _thenReturnSuccess() throws InterruptedException {

    HystrixCommand.Setter config = HystrixCommand
      .Setter
      .withGroupKey(HystrixCommandGroupKey.Factory.asKey("RemoteServiceGroupThreadPool"));

    HystrixCommandProperties.Setter commandProperties = HystrixCommandProperties.Setter();
    commandProperties.withExecutionTimeoutInMilliseconds(10_000);
    config.andCommandPropertiesDefaults(commandProperties);
    config.andThreadPoolPropertiesDefaults(HystrixThreadPoolProperties.Setter()
      .withMaxQueueSize(10)
      .withCoreSize(3)
      .withQueueSizeRejectionThreshold(10));

    assertThat(new RemoteServiceTestCommand(config, new RemoteServiceTestSimulator(500)).execute(),
      equalTo("Success"));
}
```

Defensive Programming With *Short Circuit Breaker Pattern*:
Let's consider the case that the remote service has started failing.

```java
@Test
public void givenCircuitBreakerSetup_whenRemoteSvcCmdExecuted_thenReturnSuccess()
  throws InterruptedException {

    HystrixCommand.Setter config = HystrixCommand
      .Setter
      .withGroupKey(HystrixCommandGroupKey.Factory.asKey("RemoteServiceGroupCircuitBreaker"));

    HystrixCommandProperties.Setter properties = HystrixCommandProperties.Setter();
    properties.withExecutionTimeoutInMilliseconds(1000);
    // defines the time interval after which the request to the remote service will be resumed
    properties.withCircuitBreakerSleepWindowInMilliseconds(4000);
    properties.withExecutionIsolationStrategy
     (HystrixCommandProperties.ExecutionIsolationStrategy.THREAD);
    properties.withCircuitBreakerEnabled(true);
    // defines the minimum number of requests needed before the failure rate will be considered
    properties.withCircuitBreakerRequestVolumeThreshold(1);

    config.andCommandPropertiesDefaults(properties);
    config.andThreadPoolPropertiesDefaults(HystrixThreadPoolProperties.Setter()
      .withMaxQueueSize(1)
      .withCoreSize(1)
      .withQueueSizeRejectionThreshold(1));

    assertThat(this.invokeRemoteService(config, 10_000), equalTo(null));
    assertThat(this.invokeRemoteService(config, 10_000), equalTo(null));
    assertThat(this.invokeRemoteService(config, 10_000), equalTo(null));

    Thread.sleep(5000);

    assertThat(new RemoteServiceTestCommand(config, new RemoteServiceTestSimulator(500)).execute(),
      equalTo("Success"));

    assertThat(new RemoteServiceTestCommand(config, new RemoteServiceTestSimulator(500)).execute(),
      equalTo("Success"));

    assertThat(new RemoteServiceTestCommand(config, new RemoteServiceTestSimulator(500)).execute(),
      equalTo("Success"));
}

public String invokeRemoteService(HystrixCommand.Setter config, int timeout)
  throws InterruptedException {

    String response = null;

    try {
        response = new RemoteServiceTestCommand(config,
          new RemoteServiceTestSimulator(timeout)).execute();
    } catch (HystrixRuntimeException ex) {
        System.out.println("ex = " + ex);
    }

    return response;
}
```

https://netflix.github.io/Hystrix/javadoc/com/netflix/hystrix/HystrixCommandProperties.ExecutionIsolationStrategy.html

*Isolation strategy* to use when executing a HystrixCommand.
`THREAD`: Execute the HystrixCommand.run() method on *a separate thread* and restrict concurrent executions using *the thread-pool size*.
`SEMAPHORE`: Execute the HystrixCommand.run() method on *the calling thread* and restrict concurrent executions using *the semaphore permit count*.


#### Spring Cloud Hystrix

https://www.baeldung.com/spring-cloud-netflix-hystrix

Hystrix is watching methods for failing calls to related services. If there is such a failure, it will *open the circuit* and forward the call to a *fallback method*.

The library will tolerate failures up to a *threshold*. Beyond that, it leaves the circuit open. Which means, it will forward all subsequent calls to the fallback method, to prevent future failures. This creates a time buffer for the related service to recover from its failing state.

```java
public interface GreetingController {
    @GetMapping("/greeting/{username}")
    String greeting(@PathVariable("username") String username);
}
```

```yaml
server.port=9090
spring.application.name=rest-producer
```

spring-cloud-starter-hystrix

For the Circuit Breaker to work, Hystix will scan @Component or @Service annotated classes for `@HystixCommand` annotated methods, implement a *proxy* for it and monitor its calls.

```java
@Service
public class GreetingService {
    @HystrixCommand(fallbackMethod = "defaultGreeting")
    public String getGreeting(String username) {
        return new RestTemplate()
          .getForObject("http://localhost:9090/greeting/{username}", 
          String.class, username);
    }
 
    private String defaultGreeting(String username) {
        return "Hello User!";
    }
}

@SpringBootApplication
@EnableCircuitBreaker
public class RestConsumerApplication
```

```yaml
server.port=8080
```

#### Feign

https://www.baeldung.com/intro-to-feign

Feign — a declarative HTTP client developed by Netflix.
feign-okhttp
feign-gson
feign-slf4j

BookClient bookClient = Feign.builder()
  .client(new OkHttpClient())
  .encoder(new GsonEncoder())
  .decoder(new GsonDecoder())
  .logger(new Slf4jLogger(BookClient.class))
  .logLevel(Logger.Level.FULL)
  .target(BookClient.class, "http://localhost:8081/api/books");

If we need some kind of a fallback in case of the service unavailability, we could add `HystrixFeign` to the classpath and build our client with `HystrixFeign.builder()`.

Moreover, it's also possible to add client-side load balancing and/or service discovery to our client.
We could achieve this by adding `Ribbon` to our classpath and using the builder:

BookClient bookClient = Feign.builder()
  .client(RibbonClient.create())
  .target(BookClient.class, "http://localhost:8081/api/books");

#### OpenFeign

https://blog.csdn.net/weixin_40364776/article/details/128695858

OpenFeign 使用了一种*动态代理技术*来封装远程服务调用的过程

关键步骤描述：

1. 在项目启动阶段，OpenFeign 框架会发起一个主动的扫包流程，从指定的目录下扫描并加载所有被 @FeignClient 注解修饰的接口。
2. OpenFeign 会针对每一个 *FeignClient 接口*生成一个*动态代理对象*，即图中的 FeignProxyService，这个代理对象在继承关系上属于 FeignClient 注解所修饰的接口的实例。
3. 这个动态代理对象会被添加到 Spring 上下文中，并注入到对应的服务里，也就是图中的 LocalService 服务。
4. LocalService 会发起底层方法调用。实际上这个方法调用会被 OpenFeign 生成的代理对象接管，由代理对象发起一个远程服务调用，并将调用的结果返回给 LocalService。

微服务通信之feign的*配置隔离*
https://cloud.tencent.com/developer/news/729302
SpringCloud整合Feign配置类之间的关系以及feign配置隔离的实现
https://blog.csdn.net/weixin_37689658/article/details/118482362

将@FeignClient对象的`configuration`属性对应的配置类作为成员`FeignClientSpecification`的属性注入到应用上下文。那看到这里我们就会产生一个疑问：configuration对应的配置类到底什么时候被初始化呢？最终发现在为@FeignClient*生成代理对象的时候*，他初始化了FeignClient对应的配置。如下（`NamedContextFactory.createContext`）
在为@FeignClient接口的代理对象创建了Context后，将配置初始化到了该Context。这里可以明确的是每一个@FeignClient只要name属性不一致，那么他们将拥有*不同的上下文*.



https://www.baeldung.com/spring-cloud-openfeign

Spring Cloud OpenFeign — a *declarative REST client* for Spring Boot apps.
Feign makes writing web service clients easier with pluggable annotation support, which includes *Feign annotations* and *JAX-RS annotations*.
Also, Spring Cloud adds support for *Spring MVC annotations* and for using the same `HttpMessageConverter`s as used in Spring Web.
One great thing about using Feign is that we don't have to write any code for calling the service, other than an *interface definition*.

spring-cloud-starter-openfeign

```java
@SpringBootApplication
@EnableFeignClients
public class ExampleApplication {}

@FeignClient(value = "jplaceholder", url = "https://jsonplaceholder.typicode.com/")
public interface JSONPlaceHolderClient {

    @RequestMapping(method = RequestMethod.GET, value = "/posts")
    List<Post> getPosts();

    @RequestMapping(method = RequestMethod.GET, value = "/posts/{postId}", produces = "application/json")
    Post getPostById(@PathVariable("postId") Long postId);
}
```

The `value` argument passed in the `@FeignClient` annotation is a mandatory, arbitrary client name, while with the `url` argument, we specify the API base URL.

each Feign client is composed of a set of customizable components:
- Decoder – `ResponseEntityDecoder`, which wraps SpringDecoder, used to decode the Response
- Encoder – `SpringEncoder` is used to encode the RequestBody.
- Logger – `Slf4jLogger` is the default logger used by Feign.
- Contract – `SpringMvcContract`, which provides *annotation processing*
- Feign-Builder – `HystrixFeign.Builder` is used to construct the components.
- Client – `LoadBalancerFeignClient` or default Feign client


feign-okhttp
feign-httpclient

```java
@FeignClient(value = "jplaceholder",
  url = "https://jsonplaceholder.typicode.com/",
  configuration = ClientConfiguration.class)

public class ClientConfiguration {
    @Bean
    public OkHttpClient client() {
        return new OkHttpClient();
    }
}
```

```yaml
feign:
  client:
    config:
      default:
        connectTimeout: 5000
        readTimeout: 5000
        loggerLevel: basic
```

Adding *interceptors* is another useful feature provided by Feign.

```java
@Bean
public RequestInterceptor requestInterceptor() {
  return requestTemplate -> {
      requestTemplate.header("user", username);
      requestTemplate.header("password", password);
      requestTemplate.header("Accept", ContentType.APPLICATION_JSON.getMimeType());
  };
}
```

```yaml
feign:
  client:
    config:
      default:
        requestInterceptors:
          com.baeldung.cloud.openfeign.JSONPlaceHolderInterceptor
```

```java
@Bean
public BasicAuthRequestInterceptor basicAuthRequestInterceptor() {
    return new BasicAuthRequestInterceptor("username", "password");
}
```

Feign supports Hystrix, so if we have enabled it, we can implement the *fallback pattern*.

```java
@FeignClient(value = "jplaceholder",
  url = "https://jsonplaceholder.typicode.com/",
  fallback = JSONPlaceHolderFallback.class)
public interface JSONPlaceHolderClient {
    // APIs
}
@Component
public class JSONPlaceHolderFallback implements JSONPlaceHolderClient {

    @Override
    public List<Post> getPosts() {
        return Collections.emptyList();
    }

    @Override
    public Post getPostById(Long postId) {
        return null;
    }
}
```

For each Feign client, a *logger* is created by default.

```java
public class ClientConfiguration {
    @Bean
    Logger.Level feignLoggerLevel() {
        return Logger.Level.BASIC;
    }
}
```

NONE – no logging, which is the default
BASIC – log only the request method, URL and response status
HEADERS – log the basic information together with request and response headers
FULL – log the body, headers and metadata for both request and response

Feign's default error handler, `ErrorDecoder.default`, always throws a `FeignException`.

```java
public class ClientConfiguration {
    @Bean
    public ErrorDecoder errorDecoder() {
        return new CustomErrorDecoder();
    }
}
public class CustomErrorDecoder implements ErrorDecoder {
    @Override
    public Exception decode(String methodKey, Response response) {

        switch (response.status()){
            case 400:
                return new BadRequestException();
            case 404:
                return new NotFoundException();
            default:
                return new Exception("Generic error");
        }
    }
}
```

#### Spring Cloud Netflix References

- 2.0.x: https://cloud.spring.io/spring-cloud-netflix/2.0.x/multi/multi_spring-cloud-netflix.html

##### 1. Service Discovery: Eureka Clients

*Eureka* is the Netflix Service Discovery Server and Client.

spring-cloud-starter-netflix-eureka-client

```yaml
eureka:
  client:
    serviceUrl:
      defaultZone: http://localhost:8761/eureka/
```

Having spring-cloud-starter-netflix-eureka-client on the classpath makes the app into both a Eureka "*instance*" (i.e. it registers itself) and a "*client*" (i.e. it can query the registry to locate other services). 

```java
EurekaInstanceConfigBean
EurekaClientConfigBean
```

By default, EurekaClient uses *Jersey* for HTTP communication.

You don’t have to use the raw Netflix `EurekaClient` and usually it is more convenient to use it behind a wrapper of some sort. 
Spring Cloud has support for `Feign` (a REST client builder) and also Spring `RestTemplate` using the *logical Eureka service identifiers (VIPs)* instead of physical URLs. 
To configure `Ribbon` with a fixed list of physical servers you can simply set `<client>.ribbon.listOfServers` to a comma-separated list of physical addresses (or hostnames), where `<client>` is the ID of the client.

You can also use the `org.springframework.cloud.client.discovery.DiscoveryClient` which provides a simple API for discovery clients that is not specific to Netflix

##### 2. Service Discovery: Eureka Server

spring-cloud-starter-netflix-eureka-server

`@EnableEurekaServer`

application.yml (Standalone Eureka Server). 

```yaml
server:
  port: 8761

eureka:
  instance:
    hostname: localhost
  client:
    registerWithEureka: false
    fetchRegistry: false
    serviceUrl:
      defaultZone: http://${eureka.instance.hostname}:${server.port}/eureka/
```

Set `eureka.instance.preferIpAddress` to true and when the application registers with eureka, it will use its IP Address rather than its hostname.

##### 3. Circuit Breaker: Hystrix Clients

Netflix has created a library called Hystrix that implements the *circuit breaker* pattern.

A service failure in the lower level of services can cause cascading failure all the way up to the user. 
When calls to a particular service is greater than `circuitBreaker.requestVolumeThreshold` (default: 20 requests) and failue percentage is greater than `circuitBreaker.errorThresholdPercentage` (default: >50%) in a rolling window defined by `metrics.rollingStats.timeInMilliseconds` (default: 10 seconds), the circuit opens and the call is not made. 
In cases of error and an open circuit a fallback can be provided by the developer.

spring-cloud-starter-netflix-hystrix

```java
@EnableCircuitBreaker

@Component
public class StoreIntegration {

    @HystrixCommand(fallbackMethod = "defaultStores")
    public Object getStores(Map<String, Object> parameters) {
        //do stuff that might fail
    }

    public Object defaultStores(Map<String, Object> parameters) {
        return /* something useful */;
    }
}
```

##### 4. Circuit Breaker: Hystrix Dashboard

The Hystrix Dashboard displays the health of each circuit breaker in an efficient manner.

##### 5. Hystrix Timeouts And Ribbon Clients

When using Hystrix commands that wrap Ribbon clients you want to make sure your *Hystrix timeout is configured to be longer than the configured Ribbon timeout*, *including any potential retries that might be made*. 
For example, if your Ribbon connection timeout is one second and the Ribbon client might retry the request three times, than your Hystrix timeout should be slightly more than three seconds.

spring-cloud-starter-hystrix-netflix-dashboard
`@EnableHystrixDashboard`

*Turbine* is an application that aggregates all of the relevant `/hystrix.stream` endpoints into a combined `/turbine.stream` for use in the Hystrix Dashboard. Individual instances are located via Eureka.
spring-cloud-starter-netflix-turbine
`@EnableTurbine`  

##### 6. Client Side Load Balancer: Ribbon

*Ribbon* is a *client side load balancer* which gives you a lot of control over the behaviour of HTTP and TCP clients. 
*Feign already uses Ribbon*, so if you are using `@FeignClient` then this section also applies.

spring-cloud-starter-netflix-ribbon

```java
@RibbonClient(name = "foo", configuration = FooConfiguration.class)
@Configuration
protected static class FooConfiguration {
	@Bean
	public ZonePreferenceServerListFilter serverListFilter() {
		ZonePreferenceServerListFilter filter = new ZonePreferenceServerListFilter();
		filter.setZone("myTestZone");
		return filter;
	}

	@Bean
	public IPing ribbonPing() {
		return new PingUrl();
	}
}
```

Spring Cloud Netflix provides the following beans by default for ribbon (BeanType beanName: ClassName):

`IClientConfig` ribbonClientConfig: DefaultClientConfigImpl
`IRule` ribbonRule: ZoneAvoidanceRule
`IPing` ribbonPing: DummyPing
`ServerList<Server>` ribbonServerList: ConfigurationBasedServerList
`ServerListFilter<Server>` ribbonServerListFilter: ZonePreferenceServerListFilter
`ILoadBalancer` ribbonLoadBalancer: ZoneAwareLoadBalancer
`ServerListUpdater` ribbonServerListUpdater: PollingServerListUpdater

```yaml
users:
  ribbon:
    NIWSServerListClassName: com.netflix.loadbalancer.ConfigurationBasedServerList
    NFLoadBalancerRuleClassName: com.netflix.loadbalancer.WeightedResponseTimeRule
```

The supported properties are listed below and should be prefixed by <clientName>.ribbon.:

`NFLoadBalancerClassName`: should implement ILoadBalancer
`NFLoadBalancerRuleClassName`: should implement IRule
`NFLoadBalancerPingClassName`: should implement IPing
`NIWSServerListClassName`: should implement ServerList
`NIWSServerListFilterClassName` should implement ServerListFilter


When *Eureka is used in conjunction with Ribbon* (i.e., both are on the classpath) the `ribbonServerList` is overridden with an extension of `DiscoveryEnabledNIWSServerList` which populates the list of servers from Eureka. 
It also replaces the `IPing` interface with `NIWSDiscoveryPing` which delegates to Eureka to determine if a server is up.

##### 7. Declarative REST Client: Feign

spring-cloud-starter-openfeign

```java
@EnableFeignClients

@FeignClient("stores")
public interface StoreClient {
    @RequestMapping(method = RequestMethod.GET, value = "/stores")
    List<Store> getStores();

    @RequestMapping(method = RequestMethod.POST, value = "/stores/{storeId}", consumes = "application/json")
    Store update(@PathVariable("storeId") Long storeId, Store store);
}

@FeignClient(name = "stores", configuration = FooConfiguration.class)
public interface StoreClient {
    //..
}
```

In this case the client is composed from the components already in `FeignClientsConfiguration` together with any in `FooConfiguration` (where the latter will override the former).

Spring Cloud Netflix provides the following beans by default for feign (BeanType beanName: ClassName):

`Decoder` feignDecoder: ResponseEntityDecoder (which wraps a SpringDecoder)
`Encoder` feignEncoder: SpringEncoder
`Logger` feignLogger: Slf4jLogger
`Contract` feignContract: SpringMvcContract
`Feign.Builder` feignBuilder: `HystrixFeign.Builder`
`Client` feignClient: if Ribbon is enabled it is a `LoadBalancerFeignClient`, otherwise the default feign client is used.

```yaml
feign:
  client:
    config:
      feignName:
        connectTimeout: 5000
        readTimeout: 5000
        loggerLevel: full
        errorDecoder: com.example.SimpleErrorDecoder
        retryer: com.example.SimpleRetryer
        requestInterceptors:
          - com.example.FooRequestInterceptor
          - com.example.BarRequestInterceptor
        decode404: false
```

Feign Hystrix Support
If Hystrix is on the classpath and `feign.hystrix.enabled=true`, Feign will wrap all methods with a circuit breaker.

Feign Hystrix Fallbacks

```java
@FeignClient(name = "hello", fallback = HystrixClientFallback.class)
protected interface HystrixClient {
    @RequestMapping(method = RequestMethod.GET, value = "/hello")
    Hello iFailSometimes();
}

static class HystrixClientFallback implements HystrixClient {
    @Override
    public Hello iFailSometimes() {
        return new Hello("fallback");
    }
}
```

##### 8. External Configuration: Archaius

Archaius is the Netflix client side configuration library. 
It is the library used by all of the Netflix OSS components for configuration. 
Archaius is an extension of the Apache Commons Configuration project. 
It allows updates to configuration by either *polling a source for changes* or for *a source to push changes to the client*. Archaius uses `Dynamic<Type>Property` classes as handles to properties.

##### 9. Router and Filter: Zuul

*Zuul* is a JVM based *router and server side load balancer* by Netflix.

spring-cloud-starter-netflix-zuul
`@EnableZuulProxy`

executed as a `HystrixCommand` and loadbalance multiple URLs with Ribbon

```yaml
zuul:
  routes:
    echo:
      path: /myusers/**
      serviceId: myusers-service
      stripPrefix: true

hystrix:
  command:
    myusers-service:
      execution:
        isolation:
          thread:
            timeoutInMilliseconds: ...

myusers-service:
  ribbon:
    NIWSServerListClassName: com.netflix.loadbalancer.ConfigurationBasedServerList
    ListOfServers: https://example1.com,http://example2.com
    ConnectTimeout: 1000
    ReadTimeout: 3000
    MaxTotalHttpConnections: 500
    MaxConnectionsPerHost: 100
```

##### 10. Polyglot support with Sidecar
##### 11. Metrics: Spectator, Servo, and Atlas

*Retrying Failed Requests*
Spring Cloud Netflix offers a variety of ways to make HTTP requests. 
You can use a load balanced `RestTemplate`, *Ribbon*, or *Feign*. 
No matter how you choose to your HTTP requests, there is always a chance the request may fail. 
When a request fails you may want to have the request retried automatically. 
To accomplish this when using Sping Cloud Netflix you need to include *Spring Retry* on your application’s classpath. 
When Spring Retry is present load balanced RestTemplates, Feign, and Zuul will automatically retry any failed requests (assuming you configuration allows it to).

By default no backoff policy is used when retrying requests. 
If you would like to configure a backoff policy you will need to create a bean of type `LoadBalancedBackOffPolicyFactory` which will be used to create a `BackOffPolicy` for a given service.

Anytime Ribbon is used with Spring Retry you can control the retry functionality by configuring certain Ribbon properties.

```
client.ribbon.MaxAutoRetries
client.ribbon.MaxAutoRetriesNextServer
client.ribbon.OkToRetryOnAllOperations
```

```ini
# Max number of retries on the same server (excluding the first try)
sample-client.ribbon.MaxAutoRetries=1

# Max number of next servers to retry (excluding the first server)
sample-client.ribbon.MaxAutoRetriesNextServer=1

# Whether all operations can be retried for this client
sample-client.ribbon.OkToRetryOnAllOperations=true

# Interval to refresh the server list from the source
sample-client.ribbon.ServerListRefreshInterval=2000

# Connect timeout used by Apache HttpClient
sample-client.ribbon.ConnectTimeout=3000

# Read timeout used by Apache HttpClient
sample-client.ribbon.ReadTimeout=3000

# Initial list of servers, can be changed via Archaius dynamic property at runtime
sample-client.ribbon.listOfServers=www.microsoft.com:80,www.yahoo.com:80,www.google.com:80

clientName:
  ribbon:
    retryableStatusCodes: 404,502
```

You can turn off Zuul’s retry functionality by setting `zuul.retryable` to false. You can also disable retry functionality on route by route basis by setting `zuul.routes.routename.retryable` to false.

##### 12. HTTP Clients

Spring Cloud Netflix will automatically create the HTTP client used by Ribbon, Feign, and Zuul for you. However you can also provide your own HTTP clients customized how you please yourself. To do this you can either create a bean of type `ClosableHttpClient` if you are using the Apache Http Cient, or `OkHttpClient` if you are using OK HTTP.
