.PHONY: help run clean

help:
	@echo "Usage:"
	@echo "    make run    =>  compile and run the program""
	@echo "    make clean  =>  remove .class"

run:
	@javac StateAnalyzer.java TestingFields.java
	@java StateAnalyzer

clean:
	rm -f *.class
