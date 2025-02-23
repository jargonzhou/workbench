package com.spike.microservice.dubbo.business;

import java.util.List;

import com.spike.microservice.dubbo.domain.Users;

public interface UserService {

  Integer addUser(Users user);

  List<Users> allUsers();
}
