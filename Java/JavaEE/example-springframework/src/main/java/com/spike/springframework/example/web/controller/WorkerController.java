package com.spike.springframework.example.web.controller;

import com.spike.springframework.example.context.worker.IWorker;
import com.spike.springframework.example.web.response.Result;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.web.bind.annotation.PathVariable;
import org.springframework.web.bind.annotation.PostMapping;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RestController;

import java.util.Map;

@RestController
@RequestMapping("/workers")
public class WorkerController {
    @Autowired
    private Map<String, IWorker> workerMap;

    @PostMapping("/run/{name}")
    public Result<?> runWorker(@PathVariable String name) {
        final String workerName = IWorker.BEAN_NAME_PREFIX + name;
        if (!workerMap.containsKey(workerName)) {
            return Result.builder().success(false).message("Not Found!").build();
        }

        workerMap.get(workerName).work();
        return Result.builder().success(true).build();
    }
}
