package com.spike.mybatis3.mapper;

import com.spike.mybatis3.entity.User;

public interface UserMapper {
    User selectById(Integer id);
}