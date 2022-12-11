.PHONY: help run clean

help:
	@echo "Usage:"
	@echo "    make run    =>  compile and run the program"
	@echo "    make clean  =>  remove .class"

run:
	@javac CounterClassLoader.java Dummy.java Main.java
	@java -Djava.system.class.loader=CounterClassLoader Main

clean:
	find . -name "*.class" -type f -delete
