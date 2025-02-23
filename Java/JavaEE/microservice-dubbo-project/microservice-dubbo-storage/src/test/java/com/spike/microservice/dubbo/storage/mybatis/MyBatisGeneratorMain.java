package com.spike.microservice.dubbo.storage.mybatis;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import org.mybatis.generator.api.MyBatisGenerator;
import org.mybatis.generator.config.Configuration;
import org.mybatis.generator.config.xml.ConfigurationParser;
import org.mybatis.generator.internal.DefaultShellCallback;

/**
 * MyBatis生成器工具.
 * 
 * <pre>
 * REF: http://www.mybatis.org/generator/running/runningWithJava.html
 * REF: springboot集成mybatis及mybatis generator工具使用
 * http://blog.csdn.net/travellersy/article/details/78620247
 * </pre>
 * 
 * @author zhoujiagen
 */
public class MyBatisGeneratorMain {

  public static void main(String[] args) {
    try {
      List<String> warnings = new ArrayList<String>();
      boolean overwrite = true;
      File configFile = new File("src/test/java/mybatis/generatorConfig.xml");
      ConfigurationParser cp = new ConfigurationParser(warnings);
      Configuration config = cp.parseConfiguration(configFile);
      DefaultShellCallback callback = new DefaultShellCallback(overwrite);
      MyBatisGenerator myBatisGenerator = new MyBatisGenerator(config, callback, warnings);
      myBatisGenerator.generate(null);
    } catch (Exception e) {
      e.printStackTrace();
    }

  }
}
