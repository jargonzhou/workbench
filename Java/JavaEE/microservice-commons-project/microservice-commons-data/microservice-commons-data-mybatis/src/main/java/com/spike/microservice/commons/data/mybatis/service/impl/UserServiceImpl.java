package com.spike.microservice.commons.data.mybatis.service.impl;

import java.util.List;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Service;
import org.springframework.transaction.annotation.Transactional;

import com.github.pagehelper.Page;
import com.github.pagehelper.PageHelper;
import com.spike.microservice.commons.data.mybatis.dao.mapper.UserMapper;
import com.spike.microservice.commons.data.mybatis.model.User;
import com.spike.microservice.commons.data.mybatis.service.UserService;

@Service
public class UserServiceImpl implements UserService {
  private static final Logger LOG = LoggerFactory.getLogger(UserServiceImpl.class);

  @Autowired
  private UserMapper userMapper;

  @Override
  @Transactional
  public Long addUser(User user) {
    userMapper.insert(user);
    return user.getId();
  }

  @Override
  public List<User> findUser() {
    Page<User> pageHelper = PageHelper.<User> startPage(1, 2);
    List<User> users = userMapper.selectAll();
    LOG.info("total size = {}", pageHelper.getTotal());
    PageHelper.clearPage();
    return users;
  }

}
