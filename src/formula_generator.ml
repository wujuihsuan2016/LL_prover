(* A (pseudo-)random generator of formulas *)

open Formula
open Printer
open Fctns

let in_ill = ref false
let size = ref 10
let nb = ref 0
let nb_atoms = ref 3 (* A "bound" on the number of atoms *)

let prob = ref 0.9 (* The probability of having a top-level unary operator *)

let pos_neg i in_ill = 
  let str = "X_" ^ string_of_int i in
  if in_ill then [Pos str] else [Pos str; Neg str]

type binop =
  | TENS
  | PLUS
  | WITH
  | IMPL
  | PAR

type unop = 
  | OC
  | WN

let apply_bin binop f g = match binop with
  | TENS -> Tensor (f, g)
  | PLUS -> Plus (f, g)
  | WITH -> With (f, g)
  | IMPL -> Impl (f, g)
  | PAR -> Par (f, g)

let apply_un unop f = match unop with
  | OC -> OfCourse f
  | WN -> Whynot f 

let random_formula in_ill size size1_tbl binop_tbl unop_tbl =
  let nb_size1 = Array.length size1_tbl in
  let nb_binop = Array.length binop_tbl in
  let nb_unop = Array.length unop_tbl in
  let rec aux_random size = match size with
    | 1 -> let n = Random.int nb_size1 in size1_tbl.(n)
    | 2 -> let unop = unop_tbl.(Random.int nb_unop) in
         apply_un unop (aux_random 1)
    | _ -> 
      let top_level_unop = Random.float 1.0 in match top_level_unop with
        | _ when top_level_unop > !prob -> 
            let unop = unop_tbl.(Random.int nb_unop) in
            apply_un unop (aux_random (size - 1)) 
        | _ ->
            let binop = binop_tbl.(Random.int nb_binop) in
            let i = Random.int (size - 2) in
            apply_bin binop (aux_random (i + 1)) (aux_random (size - 2 - i)) in
      aux_random size

let create_formula in_ill size nb nb_atoms = 
  let binop_tbl = 
    if in_ill then [|TENS; PLUS; WITH; IMPL|]
    else [|TENS; PLUS; WITH; PAR; IMPL|] in
  let unop_tbl = 
    if in_ill then [|OC|] else [|OC; WN|] in
  let size1_tbl = 
    let size1_list = 
      [One; Zero; Top] @ (if in_ill then [] else [Bottom]) @ 
      List.fold_left 
        (fun res i -> pos_neg i in_ill @ res) 
        [] (List.init nb_atoms (fun i -> i)) in
    Array.of_list size1_list in
  let create i = 
    Random.self_init (); 
    let formula = random_formula in_ill size size1_tbl binop_tbl unop_tbl in
    let filename = "test_formulas/" ^ (if in_ill then "ill/" else "ll/") ^
    "size_" ^ string_of_int size ^ "/" ^ string_of_int i in
    let oc = open_out filename in
    let ff = Format.formatter_of_out_channel oc in
    print_sequent_2 ff ([], [formula]);
    close_out oc
  in
  for i = 1 to nb do  
    create i;
  done

let options = 
  ["-ill", Arg.Set in_ill, "Generate formulas of ILL (LL by default)";
   "-size", Arg.Set_int size, 
   "Set the size of formulas (the default value is 10)";
   "-nb", Arg.Set_int nb, 
   "Set the number of formulas to generate (the default value is 0)"; 
   "-nb_atoms", Arg.Set_int nb_atoms, 
   "Set an upper bound on the number of different atoms (the default value is 3)"]

let usage_msg = "Usage: random_generator.byte [option]" 

let main () = 
  Arg.parse options (fun _ -> ()) usage_msg; 
  create_formula !in_ill !size !nb !nb_atoms

let () = main ()
