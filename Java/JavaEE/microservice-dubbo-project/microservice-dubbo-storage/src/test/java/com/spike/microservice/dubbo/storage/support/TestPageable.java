package com.spike.microservice.dubbo.storage.support;

public class TestPageable {

  public static void main(String[] args) {
    Pageable pageable = new Pageable(1, 2);
    // Pageable [pageNo=1, pageSize=2, orderBy=null, limit=0, offset=2]
    System.out.println(pageable);

    pageable = new Pageable(10, 3);
    // Pageable [pageNo=10, pageSize=3, orderBy=null, limit=27, offset=3]
    System.out.println(pageable);
  }
}
