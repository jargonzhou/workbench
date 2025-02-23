package com.spike.microservice.dubbo.storage.dao;

import java.util.List;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.test.annotation.Rollback;
import org.springframework.test.context.ContextConfiguration;
import org.springframework.test.context.junit4.SpringJUnit4ClassRunner;
import org.springframework.transaction.annotation.Transactional;

import com.spike.microservice.dubbo.domain.Users;
import com.spike.microservice.dubbo.storage.config.MySQLConfiguration;
import com.spike.microservice.dubbo.storage.support.Pageable;

@RunWith(SpringJUnit4ClassRunner.class)
@ContextConfiguration(classes = { MySQLConfiguration.class })
// 不要回滚
@Rollback(false)
public class TestUsersMapper {

  @Autowired
  private UsersMapper usersDao;

  @Test
  public void resources() {
    Assert.assertNotNull(usersDao);
  }

  @Test
  public void insert() {
    for (int i = 0; i < 100; i++) {
      Users record = new Users();
      record.setName("Test User " + i);
      record.setAge(31 + i);
      usersDao.insert(record);
      System.err.println(record.getId());
    }
  }

  @Transactional
  @Test
  public void paging() {
    long totalCount = usersDao.pagingCount();
    System.out.println(totalCount);
    Pageable pageable = new Pageable(2, 10);
    List<Users> data = usersDao.pagingData(pageable);
    System.out.println(data);
  }

}
