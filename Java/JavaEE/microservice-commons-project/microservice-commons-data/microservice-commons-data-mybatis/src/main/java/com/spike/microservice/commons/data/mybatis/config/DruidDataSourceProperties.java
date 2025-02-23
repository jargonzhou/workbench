package com.spike.microservice.commons.data.mybatis.config;

import org.springframework.boot.context.properties.ConfigurationProperties;
import org.springframework.context.annotation.Configuration;

@Configuration
@ConfigurationProperties(prefix = "spring.datasource.druid")
public class DruidDataSourceProperties {
  private String driverClassName;
  private String url;
  private String username;
  private String password;

  private int initialSize;
  private int minIdle;
  private int maxActive;
  private long maxWait;
  private long timeBetweenEvictionRunsMillis;
  private long minEvictableIdleTimeMillis;
  private boolean testOnBorrow;
  private boolean testOnReturn;
  private boolean testWhileIdle;
  private boolean keepAlive;
  private boolean removeAbandoned;
  private int removeAbandonedTimeout;
  private boolean logAbandoned;
  private boolean poolPreparedStatements;
  private int maxPoolPreparedStatementPerConnectionSize;
  private String filters;

  /**
   * @return the driverClassName
   */
  public String getDriverClassName() {
    return driverClassName;
  }

  /**
   * @param driverClassName the driverClassName to set
   */
  public void setDriverClassName(String driverClassName) {
    this.driverClassName = driverClassName;
  }

  /**
   * @return the url
   */
  public String getUrl() {
    return url;
  }

  /**
   * @param url the url to set
   */
  public void setUrl(String url) {
    this.url = url;
  }

  /**
   * @return the username
   */
  public String getUsername() {
    return username;
  }

  /**
   * @param username the username to set
   */
  public void setUsername(String username) {
    this.username = username;
  }

  /**
   * @return the password
   */
  public String getPassword() {
    return password;
  }

  /**
   * @param password the password to set
   */
  public void setPassword(String password) {
    this.password = password;
  }

  /**
   * @return the initialSize
   */
  public int getInitialSize() {
    return initialSize;
  }

  /**
   * @param initialSize the initialSize to set
   */
  public void setInitialSize(int initialSize) {
    this.initialSize = initialSize;
  }

  /**
   * @return the minIdle
   */
  public int getMinIdle() {
    return minIdle;
  }

  /**
   * @param minIdle the minIdle to set
   */
  public void setMinIdle(int minIdle) {
    this.minIdle = minIdle;
  }

  /**
   * @return the maxActive
   */
  public int getMaxActive() {
    return maxActive;
  }

  /**
   * @param maxActive the maxActive to set
   */
  public void setMaxActive(int maxActive) {
    this.maxActive = maxActive;
  }

  /**
   * @return the maxWait
   */
  public long getMaxWait() {
    return maxWait;
  }

  /**
   * @param maxWait the maxWait to set
   */
  public void setMaxWait(long maxWait) {
    this.maxWait = maxWait;
  }

  /**
   * @return the timeBetweenEvictionRunsMillis
   */
  public long getTimeBetweenEvictionRunsMillis() {
    return timeBetweenEvictionRunsMillis;
  }

  /**
   * @param timeBetweenEvictionRunsMillis the timeBetweenEvictionRunsMillis to set
   */
  public void setTimeBetweenEvictionRunsMillis(long timeBetweenEvictionRunsMillis) {
    this.timeBetweenEvictionRunsMillis = timeBetweenEvictionRunsMillis;
  }

  /**
   * @return the minEvictableIdleTimeMillis
   */
  public long getMinEvictableIdleTimeMillis() {
    return minEvictableIdleTimeMillis;
  }

  /**
   * @param minEvictableIdleTimeMillis the minEvictableIdleTimeMillis to set
   */
  public void setMinEvictableIdleTimeMillis(long minEvictableIdleTimeMillis) {
    this.minEvictableIdleTimeMillis = minEvictableIdleTimeMillis;
  }

  /**
   * @return the testOnBorrow
   */
  public boolean isTestOnBorrow() {
    return testOnBorrow;
  }

  /**
   * @param testOnBorrow the testOnBorrow to set
   */
  public void setTestOnBorrow(boolean testOnBorrow) {
    this.testOnBorrow = testOnBorrow;
  }

  /**
   * @return the testOnReturn
   */
  public boolean isTestOnReturn() {
    return testOnReturn;
  }

  /**
   * @param testOnReturn the testOnReturn to set
   */
  public void setTestOnReturn(boolean testOnReturn) {
    this.testOnReturn = testOnReturn;
  }

  /**
   * @return the testWhileIdle
   */
  public boolean isTestWhileIdle() {
    return testWhileIdle;
  }

  /**
   * @param testWhileIdle the testWhileIdle to set
   */
  public void setTestWhileIdle(boolean testWhileIdle) {
    this.testWhileIdle = testWhileIdle;
  }

  /**
   * @return the keepAlive
   */
  public boolean isKeepAlive() {
    return keepAlive;
  }

  /**
   * @param keepAlive the keepAlive to set
   */
  public void setKeepAlive(boolean keepAlive) {
    this.keepAlive = keepAlive;
  }

  /**
   * @return the removeAbandoned
   */
  public boolean isRemoveAbandoned() {
    return removeAbandoned;
  }

  /**
   * @param removeAbandoned the removeAbandoned to set
   */
  public void setRemoveAbandoned(boolean removeAbandoned) {
    this.removeAbandoned = removeAbandoned;
  }

  /**
   * @return the removeAbandonedTimeout
   */
  public int getRemoveAbandonedTimeout() {
    return removeAbandonedTimeout;
  }

  /**
   * @param removeAbandonedTimeout the removeAbandonedTimeout to set
   */
  public void setRemoveAbandonedTimeout(int removeAbandonedTimeout) {
    this.removeAbandonedTimeout = removeAbandonedTimeout;
  }

  /**
   * @return the logAbandoned
   */
  public boolean isLogAbandoned() {
    return logAbandoned;
  }

  /**
   * @param logAbandoned the logAbandoned to set
   */
  public void setLogAbandoned(boolean logAbandoned) {
    this.logAbandoned = logAbandoned;
  }

  /**
   * @return the poolPreparedStatements
   */
  public boolean isPoolPreparedStatements() {
    return poolPreparedStatements;
  }

  /**
   * @param poolPreparedStatements the poolPreparedStatements to set
   */
  public void setPoolPreparedStatements(boolean poolPreparedStatements) {
    this.poolPreparedStatements = poolPreparedStatements;
  }

  /**
   * @return the maxPoolPreparedStatementPerConnectionSize
   */
  public int getMaxPoolPreparedStatementPerConnectionSize() {
    return maxPoolPreparedStatementPerConnectionSize;
  }

  /**
   * @param maxPoolPreparedStatementPerConnectionSize the maxPoolPreparedStatementPerConnectionSize
   *          to set
   */
  public void
      setMaxPoolPreparedStatementPerConnectionSize(int maxPoolPreparedStatementPerConnectionSize) {
    this.maxPoolPreparedStatementPerConnectionSize = maxPoolPreparedStatementPerConnectionSize;
  }

  /**
   * @return the filters
   */
  public String getFilters() {
    return filters;
  }

  /**
   * @param filters the filters to set
   */
  public void setFilters(String filters) {
    this.filters = filters;
  }
}
