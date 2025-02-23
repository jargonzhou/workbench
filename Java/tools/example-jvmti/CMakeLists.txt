cmake_minimum_required(VERSION 3.5.0)
project(exjvmti VERSION 0.1.0 LANGUAGES C CXX)


# find / -type f -name "jvmti.h"
include_directories(
	/usr/lib/jvm/java-17-openjdk-amd64/include
  /usr/lib/jvm/java-17-openjdk-amd64/include/linux
)

option(BUILD_SHARED_LIBS "Build using shared libraries" ON)

add_library(exjvmti exjvmti.c)

include(CTest)
enable_testing()

