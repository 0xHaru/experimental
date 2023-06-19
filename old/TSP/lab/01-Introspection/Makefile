.PHONY: help run clean

help:
	@echo "Usage:"
	@echo "    make run    =>  compile and run the program"
	@echo "    make clean  =>  remove .class"

run:
	@javac DumpMethods.java
	@java DumpMethods java.lang.String

clean:
	rm -f *.class
