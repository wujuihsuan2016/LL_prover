# APLL
A Linear Logic Prover implemented in OCaml

## Usage 
### Requirements 
- OCaml >= 4.06.0 
- [Coq](https://coq.inria.fr/opam/www/using.html) 8.8.0 
  

### Compilation

To compile the LL prover,
```
make prover
```

To compile the formula generator,
```
make formulas
```

### Running tests
To view the list of available options,
```
$ ./prover.byte --help
```

To run the prover,
```
$ ./prover.byte [options] filename
$ File "filename": Provable. Execution time: 0.004000ms
```

#### Available options for the prover
- `-ill` : Choose ILL as the logical system. The system is LL by default.
- `-inv` : Ask the prover to prove the sequent using the [inverse method](http://reports-archive.adm.cs.cmu.edu/anon/2006/CMU-CS-06-162.pdf). The backward proof search is used by default.
- `-c` : Generate a proof certificate that can be verified by Coq using the [yalla](https://github.com/olaure01/yalla/tree/working) library.
- `-l` : Generate the Latex code of the proof in the fragment chosen (LL or ILL). Proofs are written in the style of sequent calculus with the package [ebproof](https://ctan.org/pkg/ebproof). Another package [cmll](https://ctan.org/pkg/cmll) is used for writing linear logic symbols.
- `-lf` : Generate the Latex code of the proof in the corresponding focused proof system (LLF or ILLF).
- `-ptree` : Output the proof tree in the internal syntax (stored in proof.apll). The BNF grammar of the output syntax is [here](./src/output_syntax.bnf).
- `-t` : Print the results on the standard output.
- `-lltp` : Set input format to [LLTP format](https://github.com/meta-logic/lltp).
- `-s [sequent]` : Write directly the sequent to prove.
- `-o [foldername]` : Set the name of the folder in which the results are
  stored. The folder will be created under `result/ll/` or `result/ill/`. The results will not be stored and printed on the standard output by
  default.
- `-ol` : Generate the latex code of the sequent.
- `-bound [number]` : Set a bound for the prover. For the backward proof search, this bound is a (pseudo-)upper bound on the number of applications of the contraction rule. For the inverse method, this is a upper bound on the number of copies of a sequent that we can use in a derived rule. Check the [thesis](http://reports-archive.adm.cs.cmu.edu/anon/2006/CMU-CS-06-162.pdf) of K. Chaudhuri for further details.

### Syntax 
A sequent is of the form ` [antecedents] |- [consequents] `, where `[antecedents]` and `[consequents]` are two comma-separated lists of formulas.

For the formulas,
- Atom : A string of characters made up of letters, digits and the underscore character. Its first character should be a letter.
- Negation of an atom `X` : `X^`  
- Tensor : `*` 
- Par : `|` 
- With : `&`
- Plus : `+`
- Lollipop (linear implication) : `-o`
- Of course : `!`
- Why not : `?`
- Top : `top`
- Bottom : `bot`
- 1 : `1`
- 0 : `0`

All unary connectives are right-associative. The binary connective `-o` is right-associative while the others are left-associative. All unary connectives have higher precedence than all binary connectives. The linear implication `-o` has the lowest precedence. No other order of precedence is assumed for the moment but some modifications are likely to be done soon.

A valid test file contains exactly a sequent and comments delimited by `(*` and `*)`.

For example, `!(!X -o Y), !(!Y -o Z) |- !X -o Z (* Provable *)` is a valid test file.

### Available tests 
There are already several tests in the folder src/Benchmarking\_tests. Most of them are collected from [here](https://github.com/carlosolarte/Benchmarking-Linear-Logic).

### Generating some tests
The formula generator allows users to generate some tests. To run the generator,
```
$ formula_generator.byte [options]
```

#### Available options for the formula generator, 
- `-ill` : Generate formulas of ILL (LL by default).
- `-size [number]` : Set the size of formulas (the default value is 10).
- `-nb [number]` : Set the number of formulas to generate (the default value is
  0).
- `-nb_atoms [number]` : Set an upper bound on the number of different atoms (the default
  value is 3).

For example, the command `formula_generator.byte -ill -size 7 -nb 10` will
generate 10 formulas of ILL of size 7 and store them in the folder
`test_formulas/ill/size_7`.
