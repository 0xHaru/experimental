.PHONY: help run clean

help:
	@echo "Usage:"
	@echo "    make run    =>  compile and run the program"
	@echo "    make clean  =>  remove .class"

run:
	@javac CounterHandler.java INestedCalls.java NestedCalls.java Main.java
	@java Main

clean:
	rm -f *.class
