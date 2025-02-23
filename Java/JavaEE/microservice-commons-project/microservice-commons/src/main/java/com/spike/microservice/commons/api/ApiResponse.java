package com.spike.microservice.commons.api;

import java.io.Serializable;
import java.util.Date;

public class ApiResponse<T> implements Serializable {

  private static final long serialVersionUID = 1L;

  private String id;
  private long time = new Date().getTime();
  private int success = 1;
  private T data;
  private String msg;
  private ApiRequest<T> request;

  public ApiResponse(ApiRequest<T> request) {
    this.request = request;
    this.id = request.getId();
  }

  public ApiResponse(ApiRequest<T> request, T data) {
    this.request = request;
    this.data = data;
    this.id = request.getId();
  }

  public ApiResponse(ApiRequest<T> request, int success, String msg) {
    this.success = success;
    this.msg = msg;
    this.request = request;
    this.id = request.getId();
  }

  public long getTime() {
    return time;
  }

  public void setTime(long time) {
    this.time = time;
  }

  public int getSuccess() {
    return success;
  }

  public void setSuccess(int success) {
    this.success = success;
  }

  public T getData() {
    return data;
  }

  public void setData(T data) {
    this.data = data;
  }

  public String getMsg() {
    return msg;
  }

  public void setMsg(String msg) {
    this.msg = msg;
  }

  public ApiRequest<T> getRequest() {
    return request;
  }

  public void setRequest(ApiRequest<T> request) {
    this.request = request;
  }

  public String getId() {
    return id;
  }

}
