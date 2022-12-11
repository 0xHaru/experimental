.PHONY: help run clean

CP=.:../javassist/javassist.jar

help:
	@echo "Usage:"
	@echo "    make run    =>  compile and run the program"
	@echo "    make clean  =>  remove .class"

run:
	@javac -cp $(CP) StringBuilderGenerator.java Main.java
	@java -cp $(CP) StringBuilderGenerator
	@jar -cf StringBuilder.jar ./java/lang/StringBuilder.class
	@java -cp $(CP) --patch-module java.base=StringBuilder.jar Main

clean:
	find . -name "*.class" -type f -delete
	find . -name "*.jar" -type f -delete

# Extended commands:
# javac --class-path .:../javassist/javassist.jar StringBuilderGenerator.java Main.java
# java  --class-path .:../javassist/javassist.jar StringBuilderGenerator
# jar   --create     --file StringBuilder.jar     ./java/lang/StringBuilder.class
# java  --class-path .:../javassist/javassist.jar --patch-module java.base=StringBuilder.jar Main
