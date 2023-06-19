#!/bin/sh
javac -cp .:../javassist/javassist.jar GenerateNestedCalls.java NestedCalls.java INestedCalls.java
java -cp .:../javassist/javassist.jar GenerateNestedCalls
java Main
