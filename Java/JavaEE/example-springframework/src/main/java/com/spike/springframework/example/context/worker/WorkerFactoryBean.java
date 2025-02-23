package com.spike.springframework.example.context.worker;

import lombok.Data;
import org.springframework.beans.factory.config.AbstractFactoryBean;

import java.util.Map;

@Data
public class WorkerFactoryBean extends AbstractFactoryBean<IWorker> {

    private Class<? extends IWorker> type;
    private String name;
    private Map<String, Object> params;

    @Override
    public Class<?> getObjectType() {
        return type;
    }

    @Override
    protected IWorker createInstance() throws Exception {
        IWorker result = type.getDeclaredConstructor().newInstance();
        result.setName(name);
        result.init(params);
        return result;
    }
}
