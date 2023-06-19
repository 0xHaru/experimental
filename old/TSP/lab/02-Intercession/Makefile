.PHONY: help run clean

help:
	@echo "Usage:"
	@echo "    make run    =>  compile and run the program"
	@echo "    make clean  =>  remove .class"

run:
	@javac InvokeUnknownMethod.java Calculator.java
	@java InvokeUnknownMethod Calculator add 7 25
	@java InvokeUnknownMethod Calculator mul 3 5
	@java InvokeUnknownMethod Calculator div 5.0 2.0
	@java InvokeUnknownMethod Calculator neg -8.0

clean:
	rm -f *.class
