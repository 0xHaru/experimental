.PHONY: help run clean

help:
	@echo "Usage:"
	@echo "    make run    =>  compile and run the program"
	@echo "    make clean  =>  remove .class"

run:
	@javac Painter.java Brush.java Toolbox.java InvokedMethods.java Edge.java Main.java
	@java Main

clean:
	rm -f *.class
