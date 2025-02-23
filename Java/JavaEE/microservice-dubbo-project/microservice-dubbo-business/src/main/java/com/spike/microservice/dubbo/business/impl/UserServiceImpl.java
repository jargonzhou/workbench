package com.spike.microservice.dubbo.business.impl;

import java.util.List;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Service;
import org.springframework.transaction.annotation.Transactional;

import com.spike.microservice.dubbo.business.UserService;
import com.spike.microservice.dubbo.domain.Users;
import com.spike.microservice.dubbo.storage.dao.UsersMapper;

@Service
public class UserServiceImpl implements UserService {

  @Autowired
  private UsersMapper userDao;

  @Transactional
  public Integer addUser(Users user) {
    userDao.insert(user);
    return user.getId();
  }

  public List<Users> allUsers() {
    return userDao.selectAll();
  }

}
