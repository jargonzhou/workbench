package com.spike.microservice.commons.support;

import java.util.UUID;

import com.google.common.base.Preconditions;

public final class IDs {

  private IDs() {
  }

  public static String next() {
    return UUID.randomUUID().toString().replaceAll("-", "");
  }

  public static String next(String serviceId) {
    Preconditions.checkArgument(serviceId != null && !"".equals(serviceId), "invalid serviceId");
    return serviceId + "." + next();
  }

}
