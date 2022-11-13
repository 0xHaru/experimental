.PHONY: help compile clean

help:
	@echo "Usage:"
	@echo "    make compile  =>  compile the project"
	@echo "    make clean    =>  remove .cmi .cmo .cmx .o files"

compile:
	ocamlc -o chem chemistry.ml
	ocamlc -o conv conversion.ml
	ocamlc -o matrix matrix.ml
	ocamlc -o freq str.cma frequencies.ml
	ocamlc -o strings strings.ml
	ocamlc -o calc str.cma polish_calc.ml

clean:
	rm chem conv matrix freq strings calc
	rm -f *.cmi *.cmo *.cmx *.o
