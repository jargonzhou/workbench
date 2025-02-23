package com.spike.microservice.springcloud.netflix.controller;

import java.util.List;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RestController;
import org.springframework.web.client.RestTemplate;

import com.netflix.appinfo.InstanceInfo;
import com.netflix.discovery.EurekaClient;
import com.netflix.discovery.shared.Application;

@RestController
public class DummyClientController {
  private static final Logger LOG = LoggerFactory.getLogger(DummyClientController.class);

  @Autowired
  private EurekaClient eurekaClient;

  @Autowired
  private RestTemplate restTemplate;

  /**
   * A sample InstanceInfo
   * 
   * <pre>
   * {
   *   "instanceId": "192.168.1.101:netflix.eureka.provider:8762",
   *   "app": "NETFLIX.EUREKA.PROVIDER",
   *   "appGroupName": null,
   *   "ipAddr": "192.168.1.101",
   *   "sid": "na",
   *   "homePageUrl": "http://192.168.1.101:8762/",
   *   "statusPageUrl": "http://192.168.1.101:8762/info",
   *   "healthCheckUrl": "http://192.168.1.101:8762/health",
   *   "secureHealthCheckUrl": null,
   *   "vipAddress": "netflix.eureka.provider",
   *   "secureVipAddress": "netflix.eureka.provider",
   *   "countryId": 1,
   *   "dataCenterInfo": {
   *     "@class": "com.netflix.appinfo.InstanceInfo$DefaultDataCenterInfo",
   *     "name": "MyOwn"
   *   },
   *   "hostName": "192.168.1.101",
   *   "status": "UP",
   *   "leaseInfo": {
   *     "renewalIntervalInSecs": 30,
   *     "durationInSecs": 90,
   *     "registrationTimestamp": 1521984522141,
   *     "lastRenewalTimestamp": 1521984522141,
   *     "evictionTimestamp": 0,
   *     "serviceUpTimestamp": 1521984522148
   *   },
   *   "isCoordinatingDiscoveryServer": false,
   *   "metadata": {
   *     "management.port": "8762",
   *     "jmx.port": "21955"
   *   },
   *   "lastUpdatedTimestamp": 1521984522148,
   *   "lastDirtyTimestamp": 1521984521608,
   *   "actionType": "ADDED",
   *   "asgName": null,
   *   "overriddenStatus": "UNKNOWN"
   * }
   * </pre>
   * 
   * @return
   */
  @RequestMapping("/hello")
  public Object hello() {
    LOG.info("ACCEPT /hello...");
    Application application = eurekaClient.getApplication("NETFLIX.EUREKA.PROVIDER");
    List<InstanceInfo> instanceInfos = application.getInstances();
    if (instanceInfos != null && instanceInfos.size() > 0) {
      InstanceInfo instanceInfo = instanceInfos.get(0);
      LOG.info("INSTANCE={}", instanceInfo);
      return instanceInfo;
    }
    return "";
  }

  @RequestMapping("/hellorest")
  public String hellorest() {
    // 直接调用Service Provider中REST接口
    return restTemplate.getForEntity("http://NETFLIX.EUREKA.PROVIDER/hello", String.class)
        .getBody();
  }
}
