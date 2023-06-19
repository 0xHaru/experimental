SOURCES = lexer.ml parser.ml main.ml
INTERFACES = lexer.mli parser.mli

.PHONY: help compile clean

help:
	@echo "Usage:"
	@echo "    make compile  =>  compile the project"
	@echo "    make clean    =>  remove .cmi .cmo .cmx .o files"

compile: $(INTERFACES) $(SOURCES)
	ocamlc -c $(INTERFACES)
	ocamlopt -o ./repl $(SOURCES)

clean:
	rm -f *.cmi *.cmo *.cmx *.o
