package com.spike.seata.order.config;

import org.springframework.cloud.openfeign.EnableFeignClients;
import org.springframework.context.annotation.Bean;
import org.springframework.context.annotation.Configuration;
import org.springframework.web.client.RestTemplate;

@Configuration
@EnableFeignClients
public class BusinessConfiguration {

    @Bean
    public RestTemplate restTemplate() {
        return new RestTemplate();
    }
}