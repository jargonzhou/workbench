package com.spike.microservice.commons.data.mybatis.service;

import java.util.List;

import com.spike.microservice.commons.data.mybatis.model.User;

public interface UserService {

  Long addUser(User user);

  List<User> findUser();
}
