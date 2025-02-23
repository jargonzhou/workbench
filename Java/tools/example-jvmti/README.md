# JVMTI example

- Windows WSL

```shell
sudo apt-get install openjdk-17-jdk
java --version
openjdk 17.0.12 2024-07-16
OpenJDK Runtime Environment (build 17.0.12+7-Ubuntu-1ubuntu220.04)
OpenJDK 64-Bit Server VM (build 17.0.12+7-Ubuntu-1ubuntu220.04, mixed mode, sharing)

javac HelloWorld.java
java HelloWorld
```

```shell
java -agentpath:/home/zhoujiagen/jvmti/build/libexjvmti.so HelloWorld

sudo cp ./build/libexjvmti.so /usr/lib/jvm/java-17-openjdk-amd64/lib/
java -agentlib:exjvmti HelloWorld
```

cleanup:

```shell
rm -rf build *.class
```