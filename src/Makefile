default: 
	ocamlbuild -use-menhir -use-ocamlfind test.byte

gen:
	ocamlbuild -use-menhir -use-ocamlfind formula_generator.byte

gen_lcm:
	ocamlbuild -use-ocamlfind sequent_generator.byte

counterexample:
	ocamlbuild -use-menhir -use-ocamlfind ll_ill.byte

formulas:
	ocamlbuild -lib unix -use-menhir -use-ocamlfind formula_generator.byte

prover: 
	ocamlbuild -lib unix -use-menhir -use-ocamlfind prover.byte

clean:
	ocamlbuild -clean
