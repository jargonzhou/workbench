# Spring Framework in Action

- 2023-03-08 Project generated using [Spring Initializr](https://start.spring.io).
- [ ] 2024-08-14 Need to upgrade the version.

# 1. `@Import` with `ImportBeanDefinitionRegistrar` 

```yaml
spike.workers:
  configs:
    hello-world:
      name: HelloWorld
      type: com.spike.springframework.example.context.worker.impl.HelloWorldWorker
      enabled: true
      params:
        greeting: Spike
    work-horse:
      name: WorkHorse
      # no type
      enabled: true
      params:
        duration: 1
```

```java
com.spike.springframework.config.ExampleContextWorkerConfig
```


```shell
curl -H "Content-Type: application/json" -X POST http://localhost:8888/workers/run/HelloWorld
{"success":true,"data":null,"message":null}

2023-03-08 22:14:07.578  INFO 12241 --- [nio-8888-exec-1] c.s.s.e.c.worker.impl.HelloWorldWorker   : HelloWorld: Spike
```