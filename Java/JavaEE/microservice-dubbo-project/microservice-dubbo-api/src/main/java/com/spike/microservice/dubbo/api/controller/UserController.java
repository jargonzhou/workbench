// package com.spike.microservice.dubbo.api.controller;
//
// import java.util.List;
//
// import org.springframework.beans.factory.annotation.Autowired;
// import org.springframework.stereotype.Controller;
// import org.springframework.web.bind.annotation.RequestMapping;
// import org.springframework.web.bind.annotation.RequestMethod;
// import org.springframework.web.bind.annotation.ResponseBody;
//
// import com.spike.microservice.dubbo.business.UserService;
// import com.spike.microservice.dubbo.domain.Users;
//
// @Controller
// @RequestMapping({ "/service/user" })
// public class UserController {
//
// @Autowired
// private UserService userService;
//
// @RequestMapping(value = { "/all" }, method = RequestMethod.GET)
// @ResponseBody
// public List<Users> all() {
// return userService.allUsers();
// }
// }
