package com.spike.springcloud.keycloak;

import org.springframework.boot.SpringApplication;
import org.springframework.boot.autoconfigure.SpringBootApplication;

@SpringBootApplication
public class KeycloakResourceServer {
    public static void main(String[] args) {
        SpringApplication.run(KeycloakResourceServer.class, args);
    }
}
