package com.spike.microservice.commons.data.mybatis.config;

import java.sql.SQLException;

import javax.sql.DataSource;

import org.mybatis.spring.annotation.MapperScan;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.context.annotation.Bean;
import org.springframework.context.annotation.Configuration;
import org.springframework.context.annotation.Primary;
import org.springframework.transaction.annotation.EnableTransactionManagement;

import com.alibaba.druid.pool.DruidDataSource;

@Configuration
@EnableTransactionManagement
@MapperScan(basePackages = "com.spike.microservice.commons.data.mybatis.dao.mapper")
public class MyBatisConfiguration {
  private static final Logger LOG = LoggerFactory.getLogger(MyBatisConfiguration.class);

  @Autowired
  private DruidDataSourceProperties druidDataSourceProperties;

  @Primary
  @Bean
  public DataSource druidDataSource() {
    DruidDataSource druidDataSource = new DruidDataSource();
    druidDataSource.setDriverClassName(druidDataSourceProperties.getDriverClassName());
    druidDataSource.setUrl(druidDataSourceProperties.getUrl());
    druidDataSource.setUsername(druidDataSourceProperties.getUsername());
    druidDataSource.setPassword(druidDataSourceProperties.getPassword());
    druidDataSource.setInitialSize(druidDataSourceProperties.getInitialSize());
    druidDataSource.setMinIdle(druidDataSourceProperties.getMinIdle());
    druidDataSource.setMaxActive(druidDataSourceProperties.getMaxActive());
    druidDataSource.setMaxWait(druidDataSourceProperties.getMaxWait());
    druidDataSource.setTimeBetweenEvictionRunsMillis(
      druidDataSourceProperties.getTimeBetweenEvictionRunsMillis());
    druidDataSource
        .setMinEvictableIdleTimeMillis(druidDataSourceProperties.getMinEvictableIdleTimeMillis());
    druidDataSource.setTestOnBorrow(druidDataSourceProperties.isTestOnBorrow());
    druidDataSource.setTestOnReturn(druidDataSourceProperties.isTestOnReturn());
    druidDataSource.setTestWhileIdle(druidDataSourceProperties.isTestWhileIdle());
    druidDataSource.setKeepAlive(druidDataSourceProperties.isKeepAlive());
    druidDataSource.setRemoveAbandoned(druidDataSourceProperties.isRemoveAbandoned());
    druidDataSource
        .setRemoveAbandonedTimeout(druidDataSourceProperties.getRemoveAbandonedTimeout());
    druidDataSource.setLogAbandoned(druidDataSourceProperties.isLogAbandoned());

    druidDataSource.setPoolPreparedStatements(druidDataSourceProperties.isPoolPreparedStatements());
    druidDataSource.setMaxPoolPreparedStatementPerConnectionSize(
      druidDataSourceProperties.getMaxPoolPreparedStatementPerConnectionSize());
    try {
      druidDataSource.setFilters(druidDataSourceProperties.getFilters());
      druidDataSource.init();
    } catch (SQLException e) {
      LOG.error("init druid datasource failed", e);
    }
    return druidDataSource;
  }

}
