echo "Build: example"
cd example
javac *.java

echo "Build: support"
cd ../support
javac *.java

echo "Build: adt"
cd ../adt
javac -classpath ../ *.java

echo "Build: sorting"
cd ../sorting
cd core
javac *.java
cd ../priority
javac -classpath ../../ *.java

echo "Build: searching"
cd ../../searching
javac -classpath ../ *.java

echo "Build: graph"
cd ../graph/core
javac -classpath ../../ *.java
cd ../cc
javac -classpath ../../ *.java
cd ../cycle
javac -classpath ../../ *.java
cd ../mst
javac -classpath ../../ *.java
cd ..
javac -classpath ../ *.java