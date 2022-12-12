.PHONY: help run clean

CP=.:../javassist/javassist.jar

help:
	@echo "Usage:"
	@echo "    make run    =>  compile and run the program"
	@echo "    make clean  =>  remove .class"

run:
	@javac -cp $(CP) *.java
	@java -cp $(CP) RunTranslator

clean:
	rm -f *.class
