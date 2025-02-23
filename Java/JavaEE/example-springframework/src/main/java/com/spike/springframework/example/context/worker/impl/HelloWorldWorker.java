package com.spike.springframework.example.context.worker.impl;

import com.spike.springframework.example.context.worker.IWorker;
import lombok.extern.slf4j.Slf4j;

import java.util.Map;

@Slf4j
public class HelloWorldWorker implements IWorker {
    public static String CONFIG_PARAM_KEY_GREETING = "greeting";

    private String name;
    private Map<String, Object> params;

    public HelloWorldWorker() {
    }


    @Override
    public void setName(String name) {
        this.name = name;
    }

    @Override
    public void init(Map<String, Object> params) {
        this.params = params;
    }

    @Override
    public void work() {
        String greeting = params.getOrDefault(CONFIG_PARAM_KEY_GREETING, CONFIG_PARAM_KEY_GREETING).toString();
        log.info(name + ": " + greeting);
    }
}
