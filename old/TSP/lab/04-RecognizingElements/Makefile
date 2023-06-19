.PHONY: help run clean

help:
	@echo "Usage:"
	@echo "    make run    =>  compile and run the program""
	@echo "    make clean  =>  remove .class"

run:
	@javac Main.java Recognizer.java DummyStack.java DummyQueue.java
	@java Main

clean:
	rm -f *.class
