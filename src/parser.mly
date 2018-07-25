%{    
   open Formula
%}

%token COMMA
%token ONE ZERO TOP BOT
%token NOT WHYNOT OFCOUR 
%token TENSOR PAR WITH PLUS IMPL LIMPL DIMPL
%token <Formula.atom> STR
%token EOF
%token LPAREN RPAREN 

%right LIMPL DIMPL
%left TENSOR PAR WITH PLUS
%right NOT WHYNOT OFCOUR

%start file
%type <Formula.sequent2> file

%%

%inline seplist(SEP, x) : l=separated_list(SEP, x) { l }

file:
  | fs=seplist(COMMA, formula) IMPL gs=seplist(COMMA, formula) EOF { (fs, gs) }

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
