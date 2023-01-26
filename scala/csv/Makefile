.PHONY: help run clean

CP=.:../lib/parser_combinators_213.jar

help:
	@echo "Usage:"
	@echo "    make run    =>  compile and run the program"
	@echo "    make clean  =>  remove .class"

run:
	@scalac -cp $(CP) Csv.scala
	@scala  -cp $(CP) Main

clean:
	rm -f *.class
	rm -rf .vscode .metals
