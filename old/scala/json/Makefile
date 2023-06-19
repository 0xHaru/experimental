.PHONY: help run clean

CP=.:../lib/parser_combinators_213.jar

help:
	@echo "Usage:"
	@echo "    make run    =>  compile and run the program"
	@echo "    make clean  =>  remove .class"

run:
	@scalac -cp $(CP) JsonParser.scala
	@scala  -cp $(CP) JsonParser
# @scalac -cp $(CP) JsonParser2.scala
# @scala  -cp $(CP) JsonParser2

clean:
	rm -f *.class
	rm -rf .vscode .metals
