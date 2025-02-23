package com.spike.microservice.commons.data.mybatis;

import java.util.Date;
import java.util.List;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.boot.test.context.SpringBootTest;
import org.springframework.test.context.junit4.SpringRunner;

import com.spike.microservice.commons.data.mybatis.model.User;
import com.spike.microservice.commons.data.mybatis.service.UserService;

@RunWith(SpringRunner.class)
@SpringBootTest
public class UserServiceTest {
  @Autowired
  private UserService userService;

  @Test
  public void testAddUser() {
    User user = new User();
    user.setName("Hello" + new Date().getTime());
    userService.addUser(user);
    System.out.println(user.getId());
  }

  @Test
  public void testQueryUser() {
    List<User> users = userService.findUser();
    for (User user : users) {
      System.out.println(user);
    }

  }
}
