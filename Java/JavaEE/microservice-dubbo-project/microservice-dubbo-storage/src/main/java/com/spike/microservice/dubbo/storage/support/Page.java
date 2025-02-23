package com.spike.microservice.dubbo.storage.support;

import java.io.Serializable;
import java.util.List;

/**
 * 分页结果.
 * @author zhoujiagen
 */
@SuppressWarnings("serial")
public class Page<T> implements Serializable {

  /** 总记录数量. */
  private long totalSize;
  /** 总页数量. */
  private long totalPageSize;
  /** 当前页号, 从1开始. */
  private long currentPage;
  /** 页中记录数量. */
  private long pageSize;
  /** 当前页中记录列表. */
  private List<T> data;

  public long getTotalSize() {
    return totalSize;
  }

  public void setTotalSize(long totalSize) {
    this.totalSize = totalSize;
  }

  public long getTotalPageSize() {
    return totalPageSize;
  }

  public void setTotalPageSize(long totalPageSize) {
    this.totalPageSize = totalPageSize;
  }

  public long getCurrentPage() {
    return currentPage;
  }

  public void setCurrentPage(long currentPage) {
    this.currentPage = currentPage;
  }

  public long getPageSize() {
    return pageSize;
  }

  public void setPageSize(long pageSize) {
    this.pageSize = pageSize;
  }

  public List<T> getData() {
    return data;
  }

  public void setData(List<T> data) {
    this.data = data;
  }
}
