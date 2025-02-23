package com.spike.springframework.example.context.worker;

import java.util.Map;

public interface IWorker {
    String CONFIG_PREFIX = "spike.workers";
    String BEAN_NAME_PREFIX = "worker.";

    void setName(String name);

    void init(Map<String, Object> params);

    void work();
}
