(* Printers *)

open Format
open Formula
open Fctns

let print_str ff s = fprintf ff "%s@?" s

let print_str_line ff s = fprintf ff "@[%s\n@]@?" s

let rec print_unop ff fmt f =
  if not (is_binop f) then
    fprintf ff fmt print_formula f
  else
    fprintf ff fmt print_formula_with_paren f

and print_binop ff fmt f g = 
  if not (is_binop f) then 
    if not (is_binop g) then
      fprintf ff fmt print_formula f print_formula g
    else
      fprintf ff fmt print_formula f print_formula_with_paren g
  else
    if not (is_binop g) then
      fprintf ff fmt print_formula_with_paren f print_formula g
    else
      fprintf ff fmt print_formula_with_paren f print_formula_with_paren g

and print_formula ff = function
  | Pos s -> print_str ff s
  | Neg s -> fprintf ff "%s^@?" s 
  | One -> fprintf ff "1@?"
  | Zero -> fprintf ff "0@?"
  | Top -> fprintf ff "top@?"
  | Bottom -> fprintf ff "bot@?"
  | OfCourse f -> print_unop ff "!%a@?" f
  | Whynot f -> print_unop ff "?%a@?" f 
  | Tensor (f, g) -> print_binop ff "%a * %a@?" f g
  | Plus (f, g) -> print_binop ff "%a + %a@?" f g 
  | With (f, g) -> print_binop ff "%a & %a@?" f g
  | Par (f, g) -> print_binop ff "%a | %a@?" f g
  | Impl (f, g) -> print_binop ff "%a -o %a@?" f g

and print_formula_with_paren ff formula = 
  fprintf ff "(%a)" print_formula formula

let print_option ff = function
  | Some f -> print_formula ff f
  | None -> print_str ff "." 

let print_sep ff () = 
  fprintf ff "%s" " , "

let print_semicolon ff () = 
  fprintf ff "%s" " ; "

let print_formula_list ff l =
  fprintf ff "@[{%a}@]" (pp_print_list ~pp_sep:print_sep print_formula) l

let rec print_formula_set ff s =
  let l = Set_formula.elements s in
  print_formula_list ff l

let print_sequent ff = function
  | Async (theta, gamma, l) ->
      fprintf ff "@[Async %a %a %a@]@?" 
      print_formula_set theta print_formula_list gamma print_formula_list l
  | Sync (theta, gamma, f) -> 
      fprintf ff "@[Sync %a %a @[%a@]@]@?"
      print_formula_set theta print_formula_list gamma print_formula f

let print_sequent_2 ff (left, right) =
  fprintf ff "%a |- %a@?"
      (pp_print_list ~pp_sep:print_sep print_formula) left 
      (pp_print_list ~pp_sep:print_sep print_formula) right

let print_rule ff = function
  | One_intro -> print_str ff "One_intro"
  | Top_intro -> print_str ff "Top_intro"
  | Bottom_intro -> print_str ff "Bottom_intro"
  | Par_intro -> print_str ff "Par_intro"
  | With_intro -> print_str ff "With_intro"
  | Tensor_intro _ -> print_str ff "Tensor_intro"
  | Plus_intro_1 -> print_str ff "Plus_intro_1"
  | Plus_intro_2 -> print_str ff "Plus_intro_2"
  | OfCourse_intro -> print_str ff "OfCourse_intro"
  | Whynot_intro -> print_str ff "Whynot_intro"
  | I1 -> print_str ff "I1"
  | I2 -> print_str ff "I2"
  | D1 _ -> print_str ff "D1"
  | D2 _ -> print_str ff "D2" 
  | R_async -> print_str ff "R_async"
  | R_sync -> print_str ff "R_sync" 

let rec print_proof ff = function
  | Null -> print_str ff "Finished"
  | Node (sequent, rule, proof_list) ->
      fprintf ff "@[%a : %a ---> %a@]" 
      print_sequent sequent print_rule rule 
      (pp_print_list print_proof) proof_list

let llf_sequent_to_ll = function
  | Async (theta, gamma, l) ->
      l @ gamma @ map_wn (Set_formula.elements theta)
  | Sync (theta, gamma, f) ->
      f :: gamma @ map_wn (Set_formula.elements theta)

(* Not finished    
let rec llf_to_ll proof = match proof with
  | Null ->  LNull
  | Node (llf_sequent, llf_rule, proof_list) -> 
      let sequent = llf_sequent_to_ll llf_sequent in
      let theta, gamma, l = 
        get_theta llf_sequent, get_gamma llf_sequent, get_list llf_sequent in
      match rule with
        | Top_intro -> LNode (sequent, LTop, LNull)
        | Bottom_intro -> 
            LNode (sequent, LTop, [llf_to_ll (List.hd proof_list)])
        | One_intro ->
            let suffix_theta = 
              List.tl (List.rev (suffix (map_wn (Set_formula.elements theta)))) in
            let rec aux l acc = match l with
              | [] -> acc 
              | hd :: tl -> 
                  aux tl (LNode (One :: hd, Lwk, acc)) in
            aux suffix_theta (LNode ([One], LOne, LNull))
        | Par_intro ->
            LNode (sequent, LPar, [llf_to_ll (List.hd proof_list)])
        | Tensor_intro (l1, l2) ->
            let proof_list' = List.map llf_to_ll proof_list in
            let theta_list = Set_formula.elements theta in
            let wn_theta_list = map_wn theta_list in 
            let suffix_theta = List.tl (suffix wn_theta_list) in
            let rec aux l acc = match l with
              | [] -> acc
              | hd :: tl ->
                  aux tl (LNode (hd @ sequent, Lcont, acc)) in
            aux suffix_theta (LNode (wn_theta_list @ sequent, LTensor, proof_list'))
        | With_intro ->
            LNode (sequent, LWith, List.map llf_to_ll proof_list)
        | Plus_intro_1 ->
            LNode (sequent, LPlus_1, List.map llf_to_ll proof_list)
        | Plus_intro_2 ->
            LNode (sequent, LPlus_2, List.map llf_to_ll proof_list)
        | OfCourse_intro ->
            LNode (sequent, LOfCourse, List.map llf_to_ll proof_list)
        | Whynot_intro ->
            if Set_formula.mem f theta then
              LNode (sequent, Lwk, List.map llf_to_ll proof_list)
            else
              llf_to_ll (List.hd proof_list)
        | I1 ->
            let theta_list = Set_formula.elements theta in
            let dual = l @ gamma in
            let suffix_theta = 
              List.tl (List.rev (suffix (map_wn theta_list))) in
            let rec aux l acc = match l with
              | [] -> acc
              | hd :: tl ->
                  aux tl (LNode (hd @ dual), Lwk, acc) in
            aux suffix_theta (LNode (dual, Lax, LNull))
        *)
 











 


                  
              


            

 



let rec print_yalla_formula ff = function
  | Pos x -> print_str ff x 
  | Neg x -> fprintf ff "(dual %s)@?" x
  | One -> print_str ff "one"
  | Zero -> print_str ff "zero"
  | Top -> print_str ff "top"
  | Bottom -> print_str ff "bot"
  | OfCourse f -> fprintf ff "(oc %a)@?" print_yalla_formula f
  | Whynot f -> fprintf ff "(wn %a)@?" print_yalla_formula f
  | Tensor (f, g) ->
      fprintf ff "(tens %a %a)@?" print_yalla_formula f print_yalla_formula g
  | Par (f, g) ->
      fprintf ff "(parr %a %a)@?" print_yalla_formula f print_yalla_formula g
  | Plus (f, g) ->
      fprintf ff "(aplus %a %a)@?" print_yalla_formula f print_yalla_formula g
  | With (f, g) ->
      fprintf ff "(awith %a %a)@?" print_yalla_formula f print_yalla_formula g
  | Impl (f, g) ->
      assert false

let print_yalla_flist ff l = 
  fprintf ff "[%a]@?" (pp_print_list ~pp_sep:print_semicolon
  print_yalla_formula) l

let rec print_ill_yalla_formula ff = function
  | Pos x -> print_str ff x
  | One -> print_str ff "ione"
  | Zero -> print_str ff "izero"
  | Top -> print_str ff "itop"
  | Bottom -> print_str ff "ibot"
  | OfCourse f -> fprintf ff "(ioc %a)@?" print_ill_yalla_formula f
  | Tensor (f, g) ->
      fprintf ff "(itens %a %a)@?" 
      print_ill_yalla_formula f print_ill_yalla_formula g
  | With (f, g) ->
      fprintf ff "(iwith %a %a)@?"
      print_ill_yalla_formula f print_ill_yalla_formula g
  | Plus (f, g) ->
      fprintf ff "(iplus %a %a)@?"
      print_ill_yalla_formula f print_ill_yalla_formula g
  | Impl (f, g) ->
      fprintf ff "(ilmap %a %a)@?"
      print_ill_yalla_formula f print_ill_yalla_formula g
  | _ ->
      assert false

let print_ill_yalla_flist ff l =
  fprintf ff "[%a]@?" 
  (pp_print_list ~pp_sep:print_semicolon print_ill_yalla_formula) l

(*let print_ill_rule ff = function
  | Tensor_L -> print_str ff "Tensor_L"
  | Tensor_R _ -> print_str ff "Tensor_R"
  | Impl_L (f, g) -> print_str ff "Impl_L"
  | Impl_R -> print_str ff "Impl_R"
  | One_L -> print_str ff "One_L"
  | One_R -> print_str ff "One_R"
  | I_R -> print_str ff "I_R"
  | Bottom_L -> print_str ff "Bottom_L"
  | Bottom_R -> print_str ff "Bottom_R"
  | Top_R -> print_str ff "Top_R"
  | Zero_L -> print_str ff "Zero_L"
  | OfCourse_L -> print_str ff "OfCourse_L"
  | OfCourse_R -> print_str ff "OfCourse_R"
  | With_R -> print_str ff "With_R"
  | With_L_1 -> print_str ff "With_L_1"
  | With_L_2 -> print_str ff "With_L_2"
  | Plus_L -> print_str ff "Plus_L"
  | Plus_R_1 -> print_str ff "Plus_R_1"
  | Plus_R_2 -> print_str ff "Plus_R_2"
  | D_L1 -> print_str ff "D_L1"
  | D_L2 -> print_str ff "D_L2"
  | D_R -> print_str ff "D_R"
  | R_L -> print_str ff "R_L"
  | R_R -> print_str ff "R_R"*)
 
(*let print_ill_sequent ff = function 
  | Pos_seq (theta, gamma, f, bl, opt) ->
      begin match opt with
        | None ->
            fprintf ff "@[Pos(%a, %a, %a, %b, _)@]@."
            print_formula_set theta
            print_formula_list gamma
            print_formula f
            bl
        | Some g ->
            fprintf ff "@[Pos(%a, %a, %a, %b, %a)@]@."
            print_formula_set theta
            print_formula_list gamma
            print_formula f
            bl
            print_formula g end
  | Neg_seq (theta, gamma, opt) ->
      match opt with
        | None ->
            fprintf ff "@[Neg(%a, %a)@]@."
            print_formula_set theta
            print_formula_list gamma
        | Some f ->
            fprintf ff "@[Neg(%a, %a, %a)@]@."
            print_formula_set theta
            print_formula_list gamma
            print_formula f *)

let print_ill_sequent ff = function
  | R_focal (theta, gamma, f) ->
      fprintf ff "@[%a | %a >> %a@]@?"
      print_formula_set theta
      print_formula_list gamma
      print_formula f
  | L_focal (theta, gamma, f, g) ->
      fprintf ff "@[%a | %a | %a << %a@]@?"
      print_formula_set theta
      print_formula_list gamma
      print_formula f
      print_formula g
  | Active (theta, gamma, omega, f) ->
      fprintf ff "@[%a | %a | %a => %a@]@?"
      print_formula_set theta 
      print_formula_list gamma
      print_formula_list omega
      print_formula f
 
