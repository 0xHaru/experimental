.PHONY: help run clean

CP=.:../lib/parser_combinators_213.jar

help:
	@echo "Usage:"
	@echo "    make run    =>  compile and run the program"
	@echo "    make setup  =>  setup the tests"
	@echo "    make clean  =>  remove .class"

run:
	@scalac -cp $(CP) LogLang.scala
	@scala  -cp $(CP) Main test/test.log

setup:
	rm -f test/*.old test/*.debug test/*.error test/*.logs
	touch test/application.debug.old
	touch test/application.debug
	touch test/access.error && echo "I'm access.error" > test/access.error
	touch test/system.error && echo "I'm system.error" > test/system.error

clean:
	rm -f *.class
	rm -rf .vscode .metals
	rm -f test/*.old test/*.debug test/*.error test/*.logs
