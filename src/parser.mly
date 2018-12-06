%{    
   open List
   open Formula
%}

%token COMMA
%token ONE ZERO TOP BOT
%token NOT WHYNOT OFCOUR 
%token TENSOR PAR WITH PLUS IMPL LIMPL DIMPL
%token <Formula.atom> STR
%token EOF
%token LPAREN RPAREN
%token FOF
%token AXIOM CONJECTURE
%token DOT

%right LIMPL DIMPL
%left TENSOR PAR WITH PLUS
%right NOT WHYNOT OFCOUR

%start file
%type <Formula.sequent2> file
%start lltp_file
%type <Formula.sequent2> lltp_file

%%

%inline seplist(SEP, x) : l=separated_list(SEP, x) { l }

file:
  | fs=seplist(COMMA, formula) IMPL gs=seplist(COMMA, formula) EOF { (fs, gs) }

lltp_file:
  | l=lltp_defs EOF { l }

lltp_defs:
  | { ([], []) }
  | f=lltp_axiom l=lltp_defs { (f::fst l, snd l) }
  | f=lltp_conjecture l=lltp_defs { (fst l, f::snd l) }

lltp_axiom:
  | FOF LPAREN STR COMMA AXIOM COMMA f=formula RPAREN DOT { f }

lltp_conjecture:
  | FOF LPAREN STR COMMA CONJECTURE COMMA f=formula RPAREN DOT { f }

formula:
  | BOT { Bottom }
  | TOP { Top }
  | ZERO { Zero }
  | ONE { One }
  | LPAREN f=formula RPAREN { f }
  | s=STR { Pos s }
  | s=STR NOT { Neg s }
  | WHYNOT f=formula { Whynot f }
  | OFCOUR f=formula { OfCourse f }
  | f=formula TENSOR g=formula { Tensor (f, g) }
  | f=formula PAR g=formula { Par (f, g) }
  | f=formula WITH g=formula { With (f, g) }
  | f=formula PLUS g=formula { Plus (f, g) }
  | f=formula LIMPL g=formula { Impl (f, g) }
  | f=formula DIMPL g=formula { With (Impl (f, g), Impl (g, f)) }
  | f=formula NOT { neg_formula f }
%%
