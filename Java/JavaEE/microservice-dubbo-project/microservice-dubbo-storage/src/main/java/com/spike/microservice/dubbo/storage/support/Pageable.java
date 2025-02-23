package com.spike.microservice.dubbo.storage.support;

import java.io.Serializable;

/**
 * @author zhoujiagen
 */
@SuppressWarnings("serial")
public class Pageable implements Serializable {
  public static final long DEFAULT_PAGE_SIZE = 10;
  /** 页号 */
  private long pageNo = 0l;
  /** 页大小 */
  private long pageSize = DEFAULT_PAGE_SIZE;

  /** 排序字段 */
  private String orderBy;

  // MySQL中获取片段数据的参数: Derived
  private long limit;
  private long offset;

  public Pageable() {
    this.calculate();
  }

  public Pageable(long pageNo) {
    this.pageNo = pageNo;
    this.calculate();
  }

  public Pageable(long pageNo, long pageSize) {
    this.pageNo = pageNo;
    this.pageSize = pageSize;
    this.calculate();
  }

  // ======================================== getter/setter
  public long getPageNo() {
    return pageNo;
  }

  public void setPageNo(long pageNo) {
    this.pageNo = pageNo;
    this.calculate();
  }

  public long getPageSize() {
    return pageSize;
  }

  public void setPageSize(long pageSize) {
    this.pageSize = pageSize;
    this.calculate();
  }

  public String getOrderBy() {
    return orderBy;
  }

  public void setOrderBy(String orderBy) {
    this.orderBy = orderBy;
  }

  public long getLimit() {
    return limit;
  }

  public long getOffset() {
    return offset;
  }

  // ========================================

  // ======================================== helper method
  private void calculate() {
    this.limit = (this.pageNo - 1) * this.pageSize;
    this.offset = this.pageSize;
  }

  @Override
  public String toString() {
    return "Pageable [pageNo=" + pageNo + ", pageSize=" + pageSize + ", orderBy=" + orderBy
        + ", limit=" + limit + ", offset=" + offset + "]";
  }

}
