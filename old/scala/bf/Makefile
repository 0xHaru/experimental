.PHONY: help run clean

CP=.:../lib/parser_combinators_213.jar

help:
	@echo "Usage:"
	@echo "    make run    =>  compile and run the program"
	@echo "    make clean  =>  remove .class"

run:
	@scalac -cp $(CP) *.scala
	@scala  -cp $(CP) BrainfuckEvaluator helloWorld.bf

clean:
	rm -f *.class
	rm -rf .vscode .metals
