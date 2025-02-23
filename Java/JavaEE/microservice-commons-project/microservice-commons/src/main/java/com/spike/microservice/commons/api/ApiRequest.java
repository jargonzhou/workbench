package com.spike.microservice.commons.api;

import java.io.Serializable;
import java.util.Date;

public class ApiRequest<T> implements Serializable {
  private static final long serialVersionUID = 1L;

  private String id; // for trace
  private long time = new Date().getTime();
  private T data;
  private ApiResponse<T> previousResponse = null; // for calling chain

  public String getId() {
    return id;
  }

  public void setId(String id) {
    this.id = id;
  }

  public T getData() {
    return data;
  }

  public void setData(T data) {
    this.data = data;
  }

  public long getTime() {
    return time;
  }

  public void setTime(long time) {
    this.time = time;
  }

  public ApiResponse<T> getPreviousResponse() {
    return previousResponse;
  }

  public void setPreviousResponse(ApiResponse<T> previousResponse) {
    this.previousResponse = previousResponse;
  }

}
