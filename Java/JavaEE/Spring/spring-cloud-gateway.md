- 4.0.4: https://docs.spring.io/spring-cloud-gateway/docs/current/reference/html/
- 使用Spring Cloud开发应用 >搭建服务网关: https://help.aliyun.com/document_detail/100229.html
- SpringCloud Gateway 基于nacos实现动态路由: https://cloud.tencent.com/developer/article/2096938

#### Tutorial

- https://www.baeldung.com/spring-cloud-gateway

The tool provides out-of-the-box *routing mechanisms* often used in microservices applications as a way of *hiding multiple services behind a single facade*.

Being focused on *routing requests*, the Spring Cloud Gateway forwards requests to a *Gateway Handler Mapping*, which determines what should be done with requests matching a specific route.

```java
@Bean
public RouteLocator customRouteLocator(RouteLocatorBuilder builder) {
    return builder.routes()
      .route("r1", r -> r.host("**.baeldung.com")
        .and()
        .path("/baeldung")
        .uri("http://baeldung.com"))
      .route(r -> r.host("**.baeldung.com")
        .and()
        .path("/myOtherRouting")
        .filters(f -> f.prefixPath("/myPrefix"))
        .uri("http://othersite.com")
        .id("myOtherID"))
    .build();
}
```

`Route` — the primary API of the gateway. It is defined by a given identification (ID), a destination (URI) and set of predicates and filters.
  `Predicate` — a Java 8 Predicate — which is used for *matching HTTP requests using headers, methods or parameters*
  `Filter` — a standard Spring `WebFilter`

```yaml
spring:
  application:
    name: gateway-service  
  cloud:
    gateway:
      routes:
      - id: baeldung
        uri: baeldung.com
      - id: myOtherRouting
        uri: localhost:9999
```

Spring Cloud Gateway *matches routes* using the *Spring WebFlux HandlerMapping infrastructure*.
It also includes many *built-in Route Predicate Factories*. All these predicates match different attributes of the HTTP request. Multiple Route Predicate Factories can be combined via the logical “and”.
Route matching can be applied both programmatically and via configuration properties file using a different type of Route Predicate Factories.

*Route filters* make the *modification* of the incoming HTTP request or outgoing HTTP response possible.
Spring Cloud Gateway includes many *built-in WebFilter Factories* as well as the possibility to create custom filters.

Spring Cloud Gateway can be easily integrated with *Service Discovery and Registry* libraries, such as Eureka Server and Consul:

```java
@Configuration
@EnableDiscoveryClient
public class GatewayDiscoveryConfiguration {
    @Bean
    public DiscoveryClientRouteDefinitionLocator 
      discoveryClientRouteLocator(DiscoveryClient discoveryClient) {
        return new DiscoveryClientRouteDefinitionLocator(discoveryClient);
    }
}
```

The `LoadBalancerClientFilter` looks for a URI in the exchange attribute property using ServerWebExchangeUtils.GATEWAY_REQUEST_URL_ATTR.
If the URL has a lb scheme (e.g., `lb://baeldung-service`), it'll use the Spring Cloud `LoadBalancerClient` to resolve the name (i.e., baeldung-service) to an actual host and port.
The unmodified original URL is placed in the ServerWebExchangeUtils.GATEWAY_ORIGINAL_REQUEST_URL_ATTR attribute.

spring-cloud-gateway
spring-cloud-starter-gateway

```yaml
spring:
  cloud:
    gateway:
      routes:
      # hitting the url “http://localhost/baeldung”, we'll be redirected to “http://baeldung.com”
      - id: baeldung_route
        uri: http://baeldung.com
        predicates:
        - Path=/baeldung/   # the path predicate
management:
  endpoints:
    web:
      exposure:
        include: "*'
```

#### References

*Clients* make requests to *Spring Cloud Gateway*. 
If the *Gateway Handler Mapping* determines that a request matches a *route*, it is sent to the *Gateway Web Handler*. 
This handler runs the request through a *filter chain* that is specific to the request. 
The reason the filters are divided by the dotted line is that filters can run logic both before and after the proxy request is sent. 
All *“pre”* filter logic is executed. Then the *proxy request* is made. After the proxy request is made, the *“post”* filter logic is run.

Configuring Route Predicate Factories and Gateway Filter Factories

```yaml
spring:
  cloud:
    gateway:
      routes:
      - id: after_route
        uri: https://example.org
        predicates:
        - name: Cookie
          args:
            name: mycookie
            regexp: mycookievalue
```

Route Predicate Factories:

```yaml
# After
# This predicate matches requests that happen after the specified datetime.
        predicates:
        - After=2017-01-20T17:42:47.789-07:00[America/Denver]
# Before
# This predicate matches requests that happen before the specified datetime. 
        predicates:
        - Before=2017-01-20T17:42:47.789-07:00[America/Denver]
# Between
# This predicate matches requests that happen after datetime1 and before datetime2.
        predicates:
        - Between=2017-01-20T17:42:47.789-07:00[America/Denver], 2017-01-21T17:42:47.789-07:00[America/Denver]
# Cookie
# This predicate matches cookies that have the given name and whose values match the regular expression
        predicates:
        - Cookie=chocolate, ch.p
# Header
# This predicate matches with a header that has the given name whose value matches the regular expression.
        predicates:
        - Header=X-Request-Id, \d+
# Host
# This predicates matches the Host header that matches the pattern.
        predicates:
        - Host=**.somehost.org,**.anotherhost.org
# Method
# the HTTP methods to match
        predicates:
        - Method=GET,POST
# Path
# a list of Spring PathMatcher patterns and an optional flag called matchTrailingSlash (defaults to true)
        predicates:
        - Path=/red/{segment},/blue/{segment}
# Query
# a required param and an optional regexp (which is a Java regular expression)
        predicates:
        - Query=green
        predicates:
        - Query=red, gree.
# RemoteAddr
# a list (min size 1) of sources, which are CIDR-notation (IPv4 or IPv6) strings, such as 192.168.0.1/16 (where 192.168.0.1 is an IP address and 16 is a subnet mask).
        predicates:
        - RemoteAddr=192.168.1.1/24
# Weight
# group and weight (an int)
# This route would forward ~80% of traffic to weighthigh.org and ~20% of traffic to weighlow.org
spring:
  cloud:
    gateway:
      routes:
      - id: weight_high
        uri: https://weighthigh.org
        predicates:
        - Weight=group1, 8
      - id: weight_low
        uri: https://weightlow.org
        predicates:
        - Weight=group1, 2                                
# XForwarded Remote Addr 
# This route predicate allows requests to be filtered based on the X-Forwarded-For HTTP header.
        predicates:
        - XForwardedRemoteAddr=192.168.1.1/24
```

GatewayFilter Factories:

```yaml
# AddRequestHeader
        filters:
        - AddRequestHeader=X-Request-red, blue

        predicates:
        - Path=/red/{segment}
        filters:
        - AddRequestHeader=X-Request-Red, Blue-{segment}
# AddRequestHeadersIfNotPresent
        filters:
        - AddRequestHeadersIfNotPresent=X-Request-Color-1:blue,X-Request-Color-2:green   
# AddRequestParameter
        filters:
        - AddRequestParameter=red, blue
# AddResponseHeader
        filters:
        - AddResponseHeader=X-Response-Red, Blue
# CircuitBreaker
# spring-cloud-starter-circuitbreaker-reactor-resilience4j
        predicates:
        - Path=/consumingServiceEndpoint
        filters:
        - name: CircuitBreaker
          args:
            name: myCircuitBreaker
            fallbackUri: forward:/inCaseOfFailureUseThis
        - RewritePath=/consumingServiceEndpoint, /backingServiceEndpoint
# CacheRequestBody
# CacheRequestBody extracts the request body and converts it to a body class (such as java.lang.String, defined in the preceding example). CacheRequestBody then places it in the attributes available from ServerWebExchange.getAttributes(), with a key defined in ServerWebExchangeUtils.CACHED_REQUEST_BODY_ATTR.
        filters:
        - name: CacheRequestBody
          args:
            bodyClass: java.lang.String
# DedupeResponseHeader
        filters:
        - DedupeResponseHeader=Access-Control-Allow-Credentials Access-Control-Allow-Origin
# FallbackHeaders
# add Spring Cloud CircuitBreaker execution exception details in the headers of a request forwarded to a fallbackUri in an external application

# JSONToGRPCFilter
# converts a JSON payload to a gRPC request    

# LocalResponseCache
# caching the response body and headers to rules

# MapRequestHeader
# takes fromHeader and toHeader parameters. It creates a new named header (toHeader), and the value is extracted out of an existing named header (fromHeader) from the incoming http request.
        filters:
        - MapRequestHeader=Blue, X-Request-Red

# ModifyRequestBody
# modify the request body before it is sent downstream by the gateway
# This filter can be configured only by using the Java DSL.

# ModifyResponseBody
# modify the response body before it is sent back to the client
# This filter can be configured only by using the Java DSL.

# PrefixPath
# a request to /hello is sent to /mypath/hello
        filters:
        - PrefixPath=/mypath

# PreserveHostHeader
# sets a request attribute that the routing filter inspects to determine if the original host header should be sent rather than the host header determined by the HTTP client. 
        filters:
        - PreserveHostHeader
        
# RedirectTo
        filters:
        - RedirectTo=302, https://acme.org

# RemoveJsonAttributesResponseBody
        filters:
        # This removes attributes "id" and "color" from the JSON content body at root level.
        - RemoveJsonAttributesResponseBody=id,color     
        filters:
        # This removes attributes "id" and "color" from the JSON content body at any level.
        - RemoveJsonAttributesResponseBody=id,color,true           

# RemoveRequestHeader
        filters:
        - RemoveRequestHeader=X-Request-Foo

# RemoveRequestParameter
        filters:
        - RemoveRequestParameter=red

# RemoveResponseHeader
        filters:
        - RemoveResponseHeader=X-Response-Foo

# RequestHeaderSize
        filters:
        # This will send a status 431 if size of any request header is greater than 1000 Bytes.
        - RequestHeaderSize=1000B

# RequestRateLimiter        
# uses a RateLimiter implementation to determine if the current request is allowed to proceed. If it is not, a status of HTTP 429 - Too Many Requests (by default) is returned.
# - spring-boot-starter-data-redis-reactive
        filters:
        - name: RequestRateLimiter
          args:
            redis-rate-limiter.replenishRate: 10
            redis-rate-limiter.burstCapacity: 20
            redis-rate-limiter.requestedTokens: 1
# - define a rate limiter as a bean that implements the RateLimiter interface
        filters:
        - name: RequestRateLimiter
          args:
            rate-limiter: "#{@myRateLimiter}"
            key-resolver: "#{@userKeyResolver}"   
            
# RewriteLocationResponseHeader
# modifies the value of the Location response header, usually to get rid of backend-specific details. 
        filters:
        - RewriteLocationResponseHeader=AS_IN_REQUEST, Location, ,  
        
# RewritePath
# rewrite the request path
        filters:
        # For a request path of /red/blue, this sets the path to /blue before making the downstream request.
        - RewritePath=/red/?(?<segment>.*), /$\{segment}     
        
# RewriteResponseHeader
# rewrite the response header value
        filters:
        - RewriteResponseHeader=X-Response-Red, , password=[^&]+, password=***
        
# SaveSession
# SecureHeaders

# SetPath
        # For a request path of /red/blue, this sets the path to /blue before making the downstream request.
        predicates:
        - Path=/red/{segment}
        filters:
        - SetPath=/{segment}

# SetRequestHeader
# replaces (rather than adding) all headers with the given name
        filters:
        - SetRequestHeader=X-Request-Red, Blue 

# SetResponseHeader
        filters:
        - SetResponseHeader=X-Response-Red, Blue

# SetStatus
        filters:
        - SetStatus=UNAUTHORIZED
        filters:
        - SetStatus=401

# StripPrefix
        # When a request is made through the gateway to /name/blue/red, the request made to nameservice looks like nameservice/red.
        predicates:
        - Path=/name/**
        filters:
        - StripPrefix=2    

# Retry
        filters:
        - name: Retry
          args:
            retries: 3
            statuses: BAD_GATEWAY
            methods: GET,POST
            backoff:
              firstBackoff: 10ms
              maxBackoff: 50ms
              factor: 2
              basedOnPreviousValue: false

# RequestSize
# sets the response status as 413 Payload Too Large with an additional header errorMessage when the request is rejected due to size. 
        filters:
        - name: RequestSize
          args:
            maxSize: 5000000 
            
# SetRequestHostHeader

# TokenRelay


spring:
  cloud:
    gateway:
      default-filters:
      - AddResponseHeader=X-Response-Default-Red, Default-Blue
      - PrefixPath=/httpbin
```

The `GlobalFilter` interface has the same signature as `GatewayFilter`. 
These are special filters that are conditionally applied to all routes.

`HttpHeadersFilters` are applied to the requests before sending them downstream, such as in the NettyRoutingFilter.


Configuration for Spring Cloud Gateway is driven by a collection of `RouteDefinitionLocator` instances.
By default, a `PropertiesRouteDefinitionLocator` loads properties by using Spring Boot’s `@ConfigurationProperties` mechanism.

You can configure additional parameters for each route by using **metadata**.


Http *timeouts* (response and connect) can be configured for all routes and overridden for each specific route.
```yaml
# global
spring:
  cloud:
    gateway:
      httpclient:
        connect-timeout: 1000
        response-timeout: 5s

# per-route
      - id: per_route_timeouts
        uri: https://example.org
        predicates:
          - name: Path
            args:
              pattern: /delay/{timeout}
        metadata:
          response-timeout: 200
          connect-timeout: 200        
```

You can configure the gateway to *create routes based on services registered with a `DiscoveryClient` compatible service registry*.
To enable this, set `spring.cloud.gateway.discovery.locator.enabled=true` and make sure a `DiscoveryClient` implementation (such as Netflix Eureka, Consul, or Zookeeper) is on the classpath and enabled.

To enable *Reactor Netty access logs*, set `-Dreactor.netty.http.server.accessLogEnabled=true`.

You can configure the gateway to control *CORS* behavior globally or per route.

```yaml
# global
spring:
  cloud:
    gateway:
      globalcors:
        cors-configurations:
          '[/**]':
            allowedOrigins: "https://docs.spring.io"
            allowedMethods:
            - GET
# per-route
spring:
  cloud:
    gateway:
      routes:
      - id: cors_route
        uri: https://example.org
        predicates:
        - Path=/service/**
        metadata:
          cors
            allowedOrigins: '*'
            allowedMethods:
              - GET
              - POST
            allowedHeaders: '*'
            maxAge: 30            
```

Configuration properties:
https://docs.spring.io/spring-cloud-gateway/docs/current/reference/html/appendix.html