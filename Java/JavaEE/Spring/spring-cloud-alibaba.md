# 源码阅读笔记模板

| Date       | Description |
| :--------- | :---------- |
| 2023-03-10 | kick off.   |

## Tips for Recapture

<!-- 帮助重温的过程总结. -->

1. 云原生应用脚手架, 版本说明
2. Reference Document

## 术语

<!-- 记录阅读过程中出现的关键字及其简单的解释. -->

## 介绍

<!-- 描述软件的来源、特性、解决的关键性问题等. -->

开源组件:

- Nacos Config
- Nacos Discovery
- Sentinel
- RocketMQ

商业化组件:

- ANS(Application Naming Service)
- Application Configuration Management(ACM) 
- OSS（Object Storage Service）
- SchedulerX（Distributed job scheduling）
- SMS（Short Message Service）

## 动机

<!-- 描述阅读软件源码的动机, 要达到什么目的等. -->

## 系统结构

<!-- 描述软件的系统结构, 核心和辅助组件的结构; 系统较复杂时细分展示. -->

## 使用

<!-- 记录软件如何使用. -->

```xml
<dependencyManagement>
    <dependencies>
        <dependency>
<groupId>com.alibaba.cloud</groupId>
<artifactId>spring-cloud-alibaba-dependencies</artifactId>
<version>2.2.9.RELEASE</version>
<type>pom</type>
<scope>import</scope>
        </dependency>
    </dependencies>
</dependencyManagement>
```


### Nacos Discovery

> Project: codes/microservice-springcloud-alibaba-project/nacosdiscovery-provider, codes/microservice-springcloud-alibaba-project/nacosdiscovery-consumer

Nacos is an easy-to-use dynamic service discovery, configuration and service management platform for building cloud native applications.

Nacos Discovery helps you to register your service to the Nacos server automatically, and the Nacos server keeps track of the services and refreshes the service list dynamically. In addition, Nacos Discovery registers some of the metadata of the service instance, such as host, port, health check URL, homepage to Nacos.

```xml
<dependency>
    <groupId>com.alibaba.cloud</groupId>
    <artifactId>spring-cloud-starter-alibaba-nacos-discovery</artifactId>
</dependency>
```

Nacos Discovery integrate with the Netflix Ribbon, RestTemplate or OpenFeign can be used for service-to-service calls.

Nacos Server: http://ip:8848 

username/password: nacos/nacos

??? example "Provider"

    ```ini
    server.port=8081
    spring.application.name=nacos-provider
    spring.cloud.nacos.discovery.server-addr=127.0.0.1:8848
    management.endpoints.web.exposure.include=*
    ```

    ```java
    @SpringBootApplication
    @EnableDiscoveryClient
    public class NacosProviderDemoApplication {

        public static void main(String[] args) {
SpringApplication.run(NacosProviderDemoApplication.class, args);
        }

        @RestController
        public class EchoController {
@GetMapping(value = "/echo/{string}")
public String echo(@PathVariable String string) {
    return "Hello Nacos Discovery " + string;
}
        }
    }
    ```

??? example "Consumer"

    ```java
    @SpringBootApplication
    @EnableDiscoveryClient
    public class NacosConsumerApp {

        @RestController
        public class NacosController{

@Autowired
private LoadBalancerClient loadBalancerClient;
@Autowired
private RestTemplate restTemplate;

@Value("${spring.application.name}")
private String appName;

@GetMapping("/echo/app-name")
public String echoAppName(){
    //Access through the combination of LoadBalanceClient and RestTemplate
    ServiceInstance serviceInstance = loadBalancerClient.choose("nacos-provider");
    String path = String.format("http://%s:%s/echo/%s",serviceInstance.getHost(),serviceInstance.getPort(),appName);
    System.out.println("request path:" +path);
    return restTemplate.getForObject(path,String.class);
}

        }

        //Instantiate RestTemplate Instance
        @Bean
        public RestTemplate restTemplate(){

return new RestTemplate();
        }

        public static void main(String[] args) {

SpringApplication.run(NacosConsumerApp.class,args);
        }
    }
    ```

### Nacos Config

> Project: codes/microservice-springcloud-alibaba-project/nacosconfig

Use Spring Cloud Alibaba Nacos Config to quickly access Nacos configuration management capabilities based on Spring Cloud’s programming model.

```xml
<dependency>
    <groupId>com.alibaba.cloud</groupId>
    <artifactId>spring-cloud-starter-alibaba-nacos-config</artifactId>
</dependency>
```

### Sentinel

> Project: codes/microservice-springcloud-alibaba-project/nacosdiscovery-consumer

Sentinel takes "flow" as the breakthrough point, and works on multiple fields including flow control, circuit breaking and load protection to protect service reliability.

```xml
<dependency>
    <groupId>com.alibaba.cloud</groupId>
    <artifactId>spring-cloud-starter-alibaba-sentinel</artifactId>
</dependency>
```

start:
```shell
java -Dserver.port=8849 -Dproject.name=sentinel-dashboard -jar sentinel-dashboard-1.8.6.jar
```


### RocketMQ Binder

> TODO

### Seata

> Project: codes/microservice-springcloud-alibaba-project/seata-business, codes/microservice-springcloud-alibaba-project/seata-storage, codes/microservice-springcloud-alibaba-project/seata-order, codes/microservice-springcloud-alibaba-project/seata-account

Seata is an **open source distributed transaction solution** dedicated to providing high performance and easy to use distributed transaction services. 
Seata will provide users with AT, TCC, SAGA, and XA transaction models to create a one-stop distributed solution for users.

- seata-examples: https://github.com/seata/seata-samples

```xml
<dependency>
    <groupId>io.seata</groupId>
    <artifactId>seata-spring-boot-starter</artifactId>
</dependency>
```

#### FAQ

MySQL Lock wait timeout:

```sql
SELECT * FROM information_schema.innodb_trx;
SELECT * FROM sys.innodb_lock_waits;
SELECT * FROM performance_schema.threads;
```

## 数据结构和算法

<!-- 描述软件中重要的数据结构和算法, 支撑过程部分的记录. -->

## 过程

<!-- 描述软件中重要的过程性内容, 例如服务器的启动、服务器响应客户端请求、服务器背景活动等. -->

## 文献引用

<!-- 记录软件相关和进一步阅读资料: 文献、网页链接等. -->

- [1] Spring Cloud Alibaba: https://spring.io/projects/spring-cloud-alibaba 
  
2.2.9.RELEASE reference: https://spring-cloud-alibaba-group.github.io/github-pages/hoxton/en-us/index.html

Example: [springcloudalibaba集成nacos+openfeign+gateway+sentinel+seata](https://dbhx.vip/article/86/0)

- [2] Code: https://github.com/alibaba/spring-cloud-alibaba

版本说明: https://github.com/alibaba/spring-cloud-alibaba/wiki/%E7%89%88%E6%9C%AC%E8%AF%B4%E6%98%8E

- [3] 云原生应用脚手架: https://start.aliyun.com/

- [4] Nacos: https://nacos.io/zh-cn/docs/what-is-nacos.html
- [5] Seata: https://seata.io/zh-cn/docs/overview/what-is-seata.html

## 其他备注
