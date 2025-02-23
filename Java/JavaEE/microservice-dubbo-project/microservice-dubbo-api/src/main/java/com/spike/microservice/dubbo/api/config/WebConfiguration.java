package com.spike.microservice.dubbo.api.config;

import java.io.IOException;
import java.util.List;

import org.springframework.boot.autoconfigure.web.servlet.WebMvcAutoConfiguration;
import org.springframework.boot.web.servlet.ServletListenerRegistrationBean;
import org.springframework.boot.web.servlet.ServletRegistrationBean;
import org.springframework.context.annotation.Bean;
import org.springframework.context.annotation.Configuration;
import org.springframework.http.converter.HttpMessageConverter;
import org.springframework.http.converter.json.Jackson2ObjectMapperBuilder;
import org.springframework.http.converter.json.MappingJackson2HttpMessageConverter;
import org.springframework.web.multipart.MultipartResolver;
import org.springframework.web.multipart.support.StandardServletMultipartResolver;
import org.springframework.web.servlet.ViewResolver;
import org.springframework.web.servlet.config.annotation.InterceptorRegistry;
import org.springframework.web.servlet.config.annotation.ResourceHandlerRegistry;
import org.springframework.web.servlet.config.annotation.ViewResolverRegistry;
import org.springframework.web.servlet.config.annotation.WebMvcConfigurer;
import org.springframework.web.servlet.view.InternalResourceViewResolver;

import com.fasterxml.jackson.databind.ObjectMapper;
import com.spike.microservice.dubbo.api.support.interceptor.IncomingRequestHandlerInterceptor;

/**
 * <pre>
 * Serving Static Web Content with Spring Boot(提供静态Web资源)
 * https://spring.io/blog/2013/12/19/serving-static-web-content-with-spring-boot
 * &#64;see WebMvcAutoConfiguration.addResourceHandlers
 * </pre>
 * 
 * @see WebMvcAutoConfiguration
 * @author zhoujiagen
 * @since 2016年10月12日 下午10:20:44
 */
@Configuration
// @EnableWebMvc
public class WebConfiguration // extends WebMvcConfigurerAdapter
    implements WebMvcConfigurer {

  // 提供静态资源处理
  // 未处理的请求转发到Servlet容器的默认servlet
  // @Override
  // public void configureDefaultServletHandling(DefaultServletHandlerConfigurer configurer) {
  // configurer.enable();
  // }

  // 资源处理器
  // 可以添加任意路径的资源
  public void addResourceHandlers(ResourceHandlerRegistry registry) {
    registry.addResourceHandler("/**")//
        .addResourceLocations("/", "/views/", "classpath:/static/")//
        .setCachePeriod(0);
  }

  /**
   * <pre>
   * 默认添加的ViewResolver
   * mvcViewResolver org.springframework.web.servlet.view.ViewResolverComposite
   * beanNameViewResolver org.springframework.web.servlet.view.BeanNameViewResolver
   * conventionErrorViewResolver org.springframework.boot.autoconfigure.web.DefaultErrorViewResolver
   * </pre>
   * 
   * @see ViewResolver
   */
  public void configureViewResolvers(ViewResolverRegistry registry) {
    InternalResourceViewResolver viewResolver =
        new InternalResourceViewResolver("/WEB-INF/jsp/", ".jsp");
    registry.viewResolver(viewResolver);
  }

  // Jackson消息转换器
  public void configureMessageConverters(List<HttpMessageConverter<?>> converters) {
    // 这里可以定制Jaskson2的ObjectMapper
    ObjectMapper objectMapper = Jackson2ObjectMapperBuilder.json().build();
    MappingJackson2HttpMessageConverter converter =
        new MappingJackson2HttpMessageConverter(objectMapper);
    converters.add(converter);
  }

  /**
   * multipart resolver: {@link StandardServletMultipartResolver}<br/>
   * drawback: cannot tuning, should configure in servlet configuration,<br/>
   * see {@link WebAppInitializer#customizeRegistration(javax.servlet.ServletRegistration.Dynamic)}
   * @return
   * @throws IOException
   */
  @Bean
  public MultipartResolver multipartResolver() throws IOException {
    return new StandardServletMultipartResolver();
  }

  // 定义拦截器
  public void addInterceptors(InterceptorRegistry registry) {
    registry.addInterceptor(new IncomingRequestHandlerInterceptor());
  }

  // Dubbo's DispatcherServlet
  @Bean
  public ServletRegistrationBean<com.alibaba.dubbo.remoting.http.servlet.DispatcherServlet>
      dubboDispatcherServlet() {
    ServletRegistrationBean<com.alibaba.dubbo.remoting.http.servlet.DispatcherServlet> bean =
        new ServletRegistrationBean<>(
            new com.alibaba.dubbo.remoting.http.servlet.DispatcherServlet(), "/http/*", "/rest/*");
    bean.setLoadOnStartup(1);
    return bean;
  }

  @Bean
  public ServletListenerRegistrationBean<com.alibaba.dubbo.remoting.http.servlet.BootstrapListener>
      BootstrapListener() {
    ServletListenerRegistrationBean<com.alibaba.dubbo.remoting.http.servlet.BootstrapListener> bean =
        new ServletListenerRegistrationBean<com.alibaba.dubbo.remoting.http.servlet.BootstrapListener>(
            new com.alibaba.dubbo.remoting.http.servlet.BootstrapListener());
    return bean;
  }
}
