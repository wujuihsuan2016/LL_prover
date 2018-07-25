(* Definition of formulas of propositional linear logic *)
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

type rule = 
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

(* Triadiac sequent *)
type sequent = 
  | Async of Set_formula.t * formula list * formula list
  | Sync of Set_formula.t * formula list * formula 

type proof = 
  | Node of sequent * rule * proof list
  | Null

let rec free_variables = function
  | Pos x | Neg x -> Set_var.of_list [x]
  | One | Zero | Top | Bottom -> Set_var.empty
  | OfCourse f | Whynot f -> free_variables f
  | Tensor (f, g) | Par (f, g) | Plus (f, g) | With (f, g) | Impl (f, g) -> 
      Set_var.union (free_variables f) (free_variables g)
   
let rec neg_formula = function
  | Pos x -> Neg x
  | Neg x -> Pos x
  | One -> Bottom
  | Zero -> Top 
  | Top -> Zero
  | Bottom -> One
  | OfCourse f -> Whynot (neg_formula f)
  | Whynot f -> OfCourse (neg_formula f)
  | Tensor (f, g) -> Par (neg_formula f, neg_formula g)
  | Par (f, g) -> Tensor (neg_formula f, neg_formula g)
  | Plus (f, g) -> With (neg_formula f, neg_formula g)
  | With (f, g) -> Plus (neg_formula f, neg_formula g)
  | Impl (f, g) -> Tensor (rewrite f, neg_formula g)

and rewrite = function
  | Impl (f, g) -> Par (neg_formula f, rewrite g)
  | OfCourse f -> OfCourse (rewrite f)
  | Whynot f -> Whynot (rewrite f)
  | Tensor (f, g) -> Tensor (rewrite f, rewrite g)
  | Par (f, g) -> Par (rewrite f, rewrite g)
  | Plus (f, g) -> Plus (rewrite f, rewrite g)
  | With (f, g) -> With (rewrite f, rewrite g)
  | f -> f

let rec string_of_formula = function
  | Pos x -> x
  | Neg x -> "(dual " ^ x ^ ")"
  | One -> "one"
  | Zero -> "zero" 
  | Top -> "top" 
  | Bottom -> "bot"
  | OfCourse f -> 
      let s = string_of_formula f in
      "(oc " ^ s ^ ")"
  | Whynot f ->
      let s = string_of_formula f in
      "(wn " ^ s ^ ")"
  | Tensor (f, g) ->
      let sf = string_of_formula f in
      let sg = string_of_formula g in
      "(tens " ^ sf ^ " " ^ sg ^ ")"
  | Par (f, g) -> 
      let sf = string_of_formula f in
      let sg = string_of_formula g in
      "(parr " ^ sf ^ " " ^ sg ^ ")"
  | Plus (f, g) ->
      let sf = string_of_formula f in
      let sg = string_of_formula g in
      "(aplus " ^ sf ^ " " ^ sg ^ ")"
  | With (f, g) ->
      let sf = string_of_formula f in
      let sg = string_of_formula g in
      "(awith " ^ sf ^ " " ^ sg ^ ")"
  | Impl (f, g) ->
      assert false 

let string_of_flist l =
  let rec string_of_list = function
    | [] -> ""
    | [x] -> string_of_formula x 
    | hd :: tl -> (string_of_formula hd) ^ "; " ^ (string_of_list tl)
  in "[" ^ string_of_list l ^ "]"

(* ILL *)

let left_sync = function
  | With _ | Top | Impl _ | Pos _ -> true
  | _ -> false

let right_sync = function
  | Tensor _ | Zero | One | OfCourse _ | Pos _ | Plus _ -> true
  | _ -> false

let left_async = function 
  | Tensor _ | Zero | One | OfCourse _ | Plus _ -> true
  | _ -> false

let right_async = function
  | With _ | Top | Impl _ -> true
  | _ -> false 

type ill_sequent = 
  | R_focal of Set_formula.t * formula list * formula
  | L_focal of Set_formula.t * formula list * formula * formula
  | Active of Set_formula.t * formula list * formula list * formula

type ill_rule = 
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

type ill_proof = 
  | INode of ill_sequent * ill_rule * ill_proof list
  | INull
