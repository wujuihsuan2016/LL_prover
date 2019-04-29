default: 
	ocamlbuild -lib unix -use-menhir -use-ocamlfind prover.byte

gen:
	ocamlbuild -lib unix -use-menhir -use-ocamlfind formula_generator.byte

gen_lcm:
	ocamlbuild -lib unix -use-ocamlfind sequent_generator.byte

counterexample:
	ocamlbuild -lib unix -use-menhir -use-ocamlfind ll_ill.byte

formulas:
	ocamlbuild -lib unix -use-menhir -use-ocamlfind formula_generator.byte

prover: 
	ocamlbuild -lib unix -use-menhir -use-ocamlfind prover.byte

translator:
	ocamlbuild -lib unix -use-menhir -use-ocamlfind translator.byte

clean:
	ocamlbuild -clean
