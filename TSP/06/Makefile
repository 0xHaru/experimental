.PHONY: help run clean

help:
	@echo "Usage:"
	@echo "    make run    =>  compile and run the program"
	@echo "    make clean  =>  remove .class"

run:
	@javac ITestingFields.java WTestingFields.java TestingFields.java StateHandler.java Main.java
	@java Main

clean:
	rm -f *.class
