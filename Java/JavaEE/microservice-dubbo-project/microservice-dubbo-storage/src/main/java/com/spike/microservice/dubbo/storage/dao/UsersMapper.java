package com.spike.microservice.dubbo.storage.dao;

import com.spike.microservice.dubbo.domain.Users;
import com.spike.microservice.dubbo.storage.support.Pageable;

import java.util.List;

public interface UsersMapper {
  int deleteByPrimaryKey(Integer id);

  int insert(Users record);

  Users selectByPrimaryKey(Integer id);

  List<Users> selectAll();

  // 分页
  long pagingCount();

  List<Users> pagingData(Pageable pageable);

  int updateByPrimaryKey(Users record);
}