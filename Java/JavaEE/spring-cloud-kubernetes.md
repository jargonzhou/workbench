Tutorial: https://www.baeldung.com/spring-cloud-kubernetes

- *service discovery* through Spring Cloud Kubernetes
- *configuration management* and injecting Kubernetes ConfigMaps and secrets to application pods using Spring Cloud Kubernetes Config
- *load balancing* using Spring Cloud Kubernetes Ribbon

Kubernetes exposes the service as a collection of *endpoints* that can be fetched and reached from within a Spring Boot Application running in a pod in the same Kubernetes cluster.
For instance, in our example, we have multiple replicas of the travel agent service, which is accessed from our client service as http://travel-agency-service:8080. However, this internally would translate into accessing different pods such as travel-agency-service-7c9cfff655-4hxnp.

spring-cloud-starter-kubernetes

```java
@SpringBootApplication
@EnableDiscoveryClient
public class Application

@RestController
public class ClientController {
    @Autowired
    private DiscoveryClient discoveryClient;
}
```

```yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: client-service
data:
  application.properties: |-
    bean.message=Testing reload! Message from backend is: %s <br/> Services : %s
```

kubectl create -f client-config.yaml

```java
@Configuration
@ConfigurationProperties(prefix = "bean")
public class ClientConfig {
  private String message = "Message from backend is: %s <br/> Services : %s";
}
```

```yaml
apiVersion: v1
kind: Secret
metadata:
  name: db-secret
data:
  username: dXNlcg==
  password: cDQ1NXcwcmQ=
```

kubectl apply -f secret.yaml

```yaml
apiVersion: extensions/v1beta1
kind: Deployment
metadata:
  name: mongo
spec:
  replicas: 1
  template:
    metadata:
      labels:
        service: mongo
      name: mongodb-service
    spec:
      containers:
      - args:
        - mongod
        - --smallfiles
        image: mongo:latest
        name: mongo
        env:
          - name: MONGO_INITDB_ROOT_USERNAME
            valueFrom:
              secretKeyRef:
                name: db-secret
                key: username
          - name: MONGO_INITDB_ROOT_PASSWORD
            valueFrom:
              secretKeyRef:
                name: db-secret
                key: password
```

```ini
spring.cloud.kubernetes.reload.enabled=true
spring.cloud.kubernetes.secrets.name=db-secret
spring.data.mongodb.host=mongodb-service
spring.data.mongodb.port=27017
spring.data.mongodb.database=admin
spring.data.mongodb.username=${MONGO_USERNAME}
spring.data.mongodb.password=${MONGO_PASSWORD}
```

```yaml
env:
  - name: MONGO_USERNAME
    valueFrom:
      secretKeyRef:
        name: db-secret
        key: username
  - name: MONGO_PASSWORD
    valueFrom:
      secretKeyRef:
        name: db-secret
        key: password
```

spring-cloud-starter-kubernetes-ribbon

```java
@RibbonClient(name = "travel-agency-service")
```

```ini
ribbon.http.client.enabled=true
```

Hystrix helps in building a fault-tolerant and resilient application. Its main aims are fail fast and rapid recovery.
`@EnableCircuitBreaker`

```java
@HystrixCommand(fallbackMethod = "getFallbackName", commandProperties = { 
    @HystrixProperty(name = "execution.isolation.thread.timeoutInMilliseconds", value = "1000") })
public String getDeals() {
    return this.restTemplate.getForObject("http://travel-agency-service:8080/deals", String.class);
}

private String getFallbackName() {
    return "Fallback";
}
```