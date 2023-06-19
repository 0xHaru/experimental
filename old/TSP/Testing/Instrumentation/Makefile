.PHONY: help run clean

CP=.:../javassist/javassist.jar

help:
	@echo "Usage:"
	@echo "    make run    =>  compile and run the program"
	@echo "    make clean  =>  remove .class"

run:
	@javac -cp $(CP) *.java
	@jar -m MANIFEST.MF -f PremainAgent.jar -c PremainAgent.class
	@java -cp $(CP) -javaagent:PremainAgent.jar Main

clean:
	rm -f *.class *.jar
