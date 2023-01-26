.PHONY: help run clean

CP=.:../lib/parser_combinators_213.jar
TEST_FILES=$(shell find test/ -name '*.desk')

help:
	@echo "Usage:"
	@echo "    make run    =>  compile and run the program"
	@echo "    make clean  =>  remove .class"

run:
	@scalac -cp $(CP) Desk.scala
	@scala  -cp $(CP) Main $(TEST_FILES)

clean:
	rm -f *.class
	rm -rf .vscode .metals
