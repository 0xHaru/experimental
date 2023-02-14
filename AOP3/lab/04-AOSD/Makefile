.PHONY: help run clean

help:
	@echo "Usage:"
	@echo "    make run    =>  compile and run the program"
	@echo "    make clean  =>  remove .class"

run:
	@ajc -1.9 *.aj *.java
	@aj ResourceWaster

clean:
	rm -f *.class
