# admin-server

未使用服务发现.

# admin-client

使用Actuator和客户端注册.

# springdoc-openapi

Swagger UI: http://localhost:18009/swagger-ui/index.html

# docker

```shell
$ mvn package
$ docker build -f Dockerfile -t docker:0.0.1-SNAPSHOT .
$ docker run -it --name docker -p 18016:18016 docker:0.0.1-SNAPSHOT

$ curl -s http://localhost:18016/
Hello, Docker!
```

# buildpacks

```shell
$ mvn spring-boot:build-image
$ docker run -it --name buildpacks \
  --env BPL_DEBUG_ENABLED=true \
  --env BPL_DEBUG_PORT=18018 \
  -p 18017:18017 \
  -p 18018:18018 \
  buildpacks:0.0.1-SNAPSHOT

$ curl -s http://localhost:18017/
Hello, Buildpacks!

# IDEA Remote JVM Debug
#-agentlib:jdwp=transport=dt_socket,server=y,suspend=n,address=*:18018
```

# jib

```shell
# build to Docker daemon
$ mvn clean package jib:dockerBuild
$ docker run -it --name jib -p 18018:80 jib:latest --rm

$ curl -s http://localhost:18018/
Hello, Jib!
```

# grafana

- Add datasource: Loki.
- Explore: loki