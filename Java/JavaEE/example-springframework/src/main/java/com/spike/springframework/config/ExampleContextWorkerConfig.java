package com.spike.springframework.config;

import com.spike.springframework.example.context.worker.WorkerProperties;
import com.spike.springframework.example.context.worker.WorkerRegistrar;
import org.springframework.boot.context.properties.EnableConfigurationProperties;
import org.springframework.context.annotation.Configuration;
import org.springframework.context.annotation.Import;

@Configuration
@Import(WorkerRegistrar.class)
// @Configuration, ImportSelector, ImportBeanDefinitionRegistrar, or regular component classes to import.
@EnableConfigurationProperties(WorkerProperties.class)
public class ExampleContextWorkerConfig {
}
