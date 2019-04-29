(*** Basic definitions of formulas, sequents and rules ***)

(** Definition of formulas of propositional linear logic **)

type atom = string

type formula = 
  | Pos of atom 
  | Neg of atom
  | One
  | Zero
  | Top
  | Bottom
  | OfCourse of formula
  | Whynot of formula
  | Tensor of formula * formula
  | Plus of formula * formula
  | With of formula * formula
  | Par of formula * formula
  | Impl of formula * formula

(** LLF **)

type llf_rule = 
  | One_intro
  | Top_intro
  | Bottom_intro
  | Par_intro
  | With_intro
  | Tensor_intro of formula list * formula list
  | Plus_intro_1
  | Plus_intro_2
  | OfCourse_intro
  | Whynot_intro
  | I1
  | I2
  | D1 of formula * formula list
  | D2 of formula
  | R_async
  | R_sync
  
module Set_formula = 
  Set.Make(struct type t = formula let compare = compare end) 

module Set_int = Set.Make(struct type t = int let compare = compare end)

module Set_var = Set.Make(struct type t = string let compare = compare end)

type sequent2 = formula list * formula list 

type llf_sequent = 
  | Async of Set_formula.t * formula list * formula list
  | Sync of Set_formula.t * formula list * formula 

type llf_proof = 
  | Node of llf_sequent * llf_rule * llf_proof list
  | Null
   
(** ILLF **)

type illf_sequent = 
  | R_focal of Set_formula.t * formula list * formula
  | L_focal of Set_formula.t * formula list * formula * formula
  | Active of Set_formula.t * formula list * formula list * formula

type illf_rule = 
  | Tensor_L 
  | Tensor_R of (formula list * formula list)
  | Impl_L of (formula list * formula list) 
  | Impl_R
  | One_L
  | One_R
  | Zero_L
  | Init
  | Top_R
  | OfCourse_L
  | OfCourse_R
  | With_R
  | With_L_1
  | With_L_2
  | Plus_L
  | Plus_R_1
  | Plus_R_2
  | Lf
  | Copy of formula
  | Rf
  | Lb
  | Rb
  | Rb_
  | Act 

type illf_proof = 
  | INode of illf_sequent * illf_rule * illf_proof list
  | INull

(** LL **)

type ll_sequent = formula list

type ll_rule = 
  | LAx
  | LTensor 
  | LPar
  | LOne
  | LBottom
  | LPlus_1
  | LPlus_2
  | LWith
  | LTop
  | Lder
  | Lwk
  | Lcont
  | LOfCourse

type ll_proof = 
  | LNode of ll_sequent * ll_rule * ll_proof list
  | LNull

(** ILL **)

type ill_sequent = formula list * formula

type ill_rule =
  | ILAx
  | ILTensor_L
  | ILTensor_R
  | ILOne_L
  | ILOne_R
  | ILImpl_L
  | ILImpl_R
  | ILPlus_L
  | ILPlus_R_1
  | ILPlus_R_2
  | ILZero_L
  | ILWith_L_1
  | ILWith_L_2
  | ILWith_R
  | ILTop_R
  | ILwk_L
  | ILcont_L
  | ILder_L
  | ILOfCourse_R

type ill_proof =
  | ILNode of ill_sequent * ill_rule * ill_proof list
  | ILNull
