#!/bin/sh
javac -cp .:../javassist/javassist.jar CustomTranslator.java RunCustomTranslator.java TestingFields.java
java  -cp .:../javassist/javassist.jar RunCustomTranslator
