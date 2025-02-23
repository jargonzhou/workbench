package com.spike.microservice.commons.data.mybatis.dao.mapper;

import com.spike.microservice.commons.data.mybatis.model.User;
import java.util.List;

import org.springframework.stereotype.Repository;

@Repository
public interface UserMapper {
  int deleteByPrimaryKey(Long id);

  int insert(User record);

  User selectByPrimaryKey(Long id);

  List<User> selectAll();

  int updateByPrimaryKey(User record);
}