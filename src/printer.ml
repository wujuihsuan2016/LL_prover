(*** Pretty-printing ***)

open Format
open Formula
open Fctns

(* [print_str ff s] outputs the string [s] on the formatter [ff]. *)
let print_str ff s = fprintf ff "%s@?" s

(* [print_str_line ff s] outputs the string [s] and a newline on the formatter
   [ff]. *)
let print_str_line ff s = fprintf ff "@[%s\n@]@?" s

(* [print_unop ff fmt f] outputs the formula [f] on the formatter [ff]
   according to the format [fmt] when we attempts to print [#f] (# is a unary
   connective). *)
let rec print_unop ff fmt f =
  if not (is_binop f) then
    fprintf ff fmt print_formula f
  else
    fprintf ff fmt print_formula_with_paren f

(* [print_binop ff fmt f g outputs the formulas [f] and [g] on the formatter
   [ff] according to the format [fmt] when we attempts to print [f#g] (# is a
   binary connective). *)
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

(* [print_formula ff f] outputs the formula [f] on the formatter [ff]. *)
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

(* [print_formula_with_paren ff f] outputs the formula [f] enclosed in
   parentheses on the formatter [ff]. *)
and print_formula_with_paren ff formula = 
  fprintf ff "(%a)" print_formula formula

(* [print_option ff op] outputs the formula [f] on the formatter [ff] if [op] =
   [Some f]. Otherwise, a dot is printed. *)
let print_option ff = function
  | Some f -> print_formula ff f
  | None -> print_str ff "." 

(* [printer sep ff ()] outputs a comma on the formatter [ff]. *)
let print_sep ff () = 
  fprintf ff "%s" " , "

(* [print_semicolon ff ()] outputs a semicolon on the formatter [ff]. *)
let print_semicolon ff () = 
  fprintf ff "%s" " ; "

(* [print_formula_list ff l] outputs the list of formulas [l] separated by
   commas and enclosed in braces on the formatter [ff]. *)
let print_formula_list ff l =
  fprintf ff "@[{%a}@]" (pp_print_list ~pp_sep:print_sep print_formula) l

(* [print_formula_set ff s] outputs the members of [s] separated by commas and
   enclosed in braces on the formatter [ff]. *)
let rec print_formula_set ff s =
  let l = Set_formula.elements s in
  print_formula_list ff l

(* [print_llf_sequent ff s] outputs the LLF sequent [s] on the formatter [ff].
   *)
let print_llf_sequent ff = function
  | Async (theta, gamma, l) ->
      fprintf ff "@[Async %a %a %a@]@?" 
      print_formula_set theta print_formula_list gamma print_formula_list l
  | Sync (theta, gamma, f) -> 
      fprintf ff "@[Sync %a %a @[%a@]@]@?"
      print_formula_set theta print_formula_list gamma print_formula f

(* [print_sequent_2 ff (left, right) outputs the two-sided sequent
   [(left,right)] on the formatter [f]. *)
let print_sequent_2 ff (left, right) =
  fprintf ff "%a |- %a@?"
      (pp_print_list ~pp_sep:print_sep print_formula) left 
      (pp_print_list ~pp_sep:print_sep print_formula) right

(* [print_llf_rule ff r] outputs the LLF rule [r] on the formatter [ff]. *)
let print_llf_rule ff = function
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

(* [print_llf_proof ff p] outputs the LLF proof [p] on the formatter [ff]. *)
let rec print_llf_proof ff = function
  | Null -> print_str ff "Finished"
  | Node (sequent, rule, proof_list) ->
      fprintf ff "@[%a : %a ---> %a@]"
      print_llf_sequent sequent print_llf_rule rule
      (pp_print_list print_llf_proof) proof_list

(** Pretty-printing of LL proofs **)

(* [llf_to_ll_sequent s] translates the LLF sequent [s] into the corresponding
   LL sequent. *)
let llf_to_ll_sequent = function
  | Async (theta, gamma, l) ->
      l @ gamma @ map_wn (Set_formula.elements theta)
  | Sync (theta, gamma, f) ->
      f :: gamma @ map_wn (Set_formula.elements theta)

(* [llf_to_ll_proof proof] translates the LLF proof [proof] into the
   corresponding LL proof. *)
let rec llf_to_ll_proof proof = match proof with
  | Null ->  LNull
  | Node (llf_sequent, llf_rule, proof_list) -> 
      let sequent = llf_to_ll_sequent llf_sequent in
      let theta, gamma, l = 
        get_theta llf_sequent, get_gamma llf_sequent, get_list llf_sequent in
      let theta_list = Set_formula.elements theta in
      match llf_rule with
        | Top_intro -> LNode (sequent, LTop, [LNull])
        | Bottom_intro -> 
            LNode (sequent, LTop, [llf_to_ll_proof (List.hd proof_list)])
        | One_intro ->
            let suffix_theta = 
              List.tl (List.rev (suffix (map_wn theta_list)))
            in
            let rec aux l acc = match l with
              | [] -> acc
              | hd :: tl -> 
                  aux tl (LNode (One :: hd, Lwk, [acc])) in
            aux suffix_theta (LNode ([One], LOne, [LNull]))
        | Par_intro ->
            LNode (sequent, LPar, [llf_to_ll_proof (List.hd proof_list)])
        | Tensor_intro (l1, l2) ->
            let proof_list' = List.map llf_to_ll_proof proof_list in
            let wn_theta_list = map_wn theta_list in 
            let suffix_theta = List.tl (suffix wn_theta_list) in
            let rec aux l acc = match l with
              | [] -> acc
              | hd :: tl ->
                  aux tl (LNode (hd @ sequent, Lcont, [acc])) in
            aux suffix_theta
                (LNode (wn_theta_list @ sequent, LTensor, proof_list'))
        | With_intro ->
            LNode (sequent, LWith, List.map llf_to_ll_proof proof_list)
        | Plus_intro_1 ->
            LNode (sequent, LPlus_1, List.map llf_to_ll_proof proof_list)
        | Plus_intro_2 ->
            LNode (sequent, LPlus_2, List.map llf_to_ll_proof proof_list)
        | OfCourse_intro ->
            LNode (sequent, LOfCourse, List.map llf_to_ll_proof proof_list)
        | Whynot_intro ->
            let f, l' =
              match l with Whynot f :: l' -> (f, l') | _ -> assert false in
            if Set_formula.mem f theta then
              LNode (sequent, Lwk, List.map llf_to_ll_proof proof_list)
            else
              llf_to_ll_proof (List.hd proof_list)
        | I1 ->
            let dual = l @ gamma in
            let suffix_theta = 
              List.tl (List.rev (suffix (map_wn theta_list))) in
            let rec aux l acc = match l with
              | [] -> acc
              | hd :: tl ->
                  aux tl (LNode (hd @ dual, Lwk, [acc])) in
            aux suffix_theta (LNode (dual, LAx, [LNull]))
        | I2 ->
            let x = match l with [Pos x] -> x | _ -> assert false in
            let theta'_list = 
              Set_formula.elements (Set_formula.remove (Neg x) theta) in
            let suffix_theta =
              List.tl (List.rev (suffix (map_wn theta'_list))) in
            let rec aux l acc = match l with
              | [] -> acc
              | hd :: tl ->
                  aux tl (LNode (hd @ [Whynot (Neg x); Pos x], Lwk, [acc])) in
            let acc =
              LNode ([Whynot (Neg x); Pos x], Lder, [LNode ([Neg x; Pos x], LAx,
              [LNull])]) in
            aux suffix_theta acc
        | D1 _ -> llf_to_ll_proof (List.hd proof_list)
        | D2 f -> 
            LNode 
              (sequent, Lcont, 
              [LNode (Whynot f :: sequent, Lder,
                      [llf_to_ll_proof (List.hd proof_list)])])
        | _ -> llf_to_ll_proof (List.hd proof_list)

(* [print_ll_rule ff rule] outputs the LL rule [rule] on the formatter [ff]. *)
let print_ll_rule ff = function
  | LAx -> print_str ff "Ax"
  | LTensor -> print_str ff "Tensor"
  | LPar -> print_str ff "Par"
  | LOne -> print_str ff "One"
  | LBottom -> print_str ff "Bottom"
  | LPlus_1 -> print_str ff "Plus_1"
  | LPlus_2 -> print_str ff "Plus_2"
  | LWith -> print_str ff "With"
  | LTop -> print_str ff "Top"
  | Lder -> print_str ff "der"
  | Lwk -> print_str ff "wk"
  | Lcont -> print_str ff "cont"
  | LOfCourse -> print_str ff "OfCourse"

(* [print_ll_sequent ff seq] outputs the LL sequent [seq] on the formatter [ff].
   *)
let print_ll_sequent ff =
  fprintf ff "%a" (pp_print_list ~pp_sep:print_sep print_formula)

(* [print_ll_proof ff proof] outputs the LL proof [proof] on the formatter [ff].
   *)
let rec print_ll_proof ff = function
  | LNode (seq, r, proof_list) ->
      fprintf ff "@[(%a -> %a -> [%a])@]@?"
      print_ll_sequent seq
      print_ll_rule r
      print_ll_proof_list proof_list
  | LNull -> ()

(* [print_ll_proof_list ff proof_list] outputs the list [proof_list] of LL
   proofs on the formatter [ff]. *)
and print_ll_proof_list ff proof_list =
  fprintf ff "@[%a@]@?"
  (pp_print_list ~pp_sep:print_sep print_ll_proof) proof_list

(* [output_proof_ll proof filename] writes the LL proof corresponding to the
   LLF proof [proof] into the file [filename]. *)
let output_proof_ll proof filename =
  let oc = open_out filename in
  let ff = formatter_of_out_channel oc in
  print_ll_proof ff (llf_to_ll_proof proof);
  close_out oc

(** Pretty-printing of ILL proofs **)

(* [illf_sequent_to_ill seq] returns the ILL sequent corresponding to the ILLF
   sequent [seq]. *)
let illf_sequent_to_ill = function
  | R_focal (theta, gamma, f) -> map_oc theta @ gamma, f
  | L_focal (theta, gamma, f, g) -> map_oc theta @ (f :: gamma), g
  | Active (theta, gamma, omega, f) -> map_oc theta @ omega @ gamma, f

let (++) l1 (l2, f) = (l1 @ l2, f)

(* [cont_theta oc_theta sequent proof] extends the proof [proof] by applying a
   sequence of contractions (backwards) that duplicates the unrestricted zone
   [oc_theta] to [sequent]. *)
let cont_theta oc_theta sequent proof =
  let suffix_theta = List.tl (suffix oc_theta) in
  let rec aux l acc = match l with
    | [] -> acc
    | hd :: tl ->
        let acc = ILNode (hd ++ sequent, ILcont_L, [acc]) in
        aux tl acc
  in
  aux suffix_theta proof

(* [wk_theta oc_theta sequent proof] extends the proof [proof] by applying a
   sequence of contractions (backwards) that eliminates the unrestricted zone
   [oc_theta] to [sequent]. *)
let wk_theta oc_theta sequent proof =
  let suffix_theta = List.tl (List.rev (suffix oc_theta)) in
  let rec aux l acc = match l with
    | [] -> acc
    | hd :: tl ->
        let acc = ILNode (hd ++ sequent, ILwk_L, [acc]) in
        aux tl acc
  in
  aux suffix_theta proof

(* [illf_to_ill proof] translated the ILLF proof [proof] into an ILL proof. *)
let rec illf_to_ill_proof proof = match proof with
  | INull -> ILNull
  | INode (illf_sequent, illf_rule, proof_list) ->
      let theta, gamma, formula =
        ill_get_theta illf_sequent, ill_get_gamma illf_sequent,
        ill_get_formula illf_sequent in
      let oc_theta = map_oc theta in
      let sequent = illf_sequent_to_ill illf_sequent in
      let proof_list = List.map illf_to_ill_proof proof_list in
      match illf_rule with
        | Tensor_L ->
            ILNode (sequent, ILTensor_L, proof_list)
        | Tensor_R (gamma1, gamma2) ->
            cont_theta oc_theta sequent
            (ILNode (oc_theta ++ sequent, ILTensor_R, proof_list))
        | Impl_L (gamma1, gamma2) ->
            cont_theta oc_theta sequent
            (ILNode (oc_theta ++ sequent, ILImpl_L, proof_list))
        | Impl_R ->
            ILNode (sequent, ILImpl_R, proof_list)
        | One_L ->
            ILNode (sequent, ILOne_L, proof_list)
        | One_R ->
            wk_theta oc_theta ([], One)
            (ILNode (([], One), ILOne_R, [ILNull]))
        | Init ->
            wk_theta oc_theta ([formula], formula)
            (ILNode (([formula], formula), ILAx, [ILNull]))
        | Top_R ->
            ILNode (sequent, ILTop_R, [ILNull])
        | Zero_L ->
            ILNode (sequent, ILZero_L, [ILNull])
        | OfCourse_L ->
            let f =
              match List.hd gamma with OfCourse f -> f | _ -> assert false in
            if Set_formula.mem f theta then
              ILNode (sequent, ILwk_L, proof_list)
            else List.hd proof_list
        | OfCourse_R ->
            ILNode (sequent, ILOfCourse_R, proof_list)
        | With_R ->
            cont_theta oc_theta sequent
            (ILNode (oc_theta ++ sequent, ILWith_R, proof_list))
        | With_L_1 ->
            ILNode (sequent, ILWith_L_1, proof_list)
        | With_L_2 ->
            ILNode (sequent, ILWith_L_2, proof_list)
        | Plus_L ->
            cont_theta oc_theta sequent
            (ILNode (oc_theta ++ sequent, ILPlus_L, proof_list))
        | Plus_R_1 ->
            ILNode (sequent, ILPlus_R_1, proof_list)
        | Plus_R_2 ->
            ILNode (sequent, ILPlus_R_2, proof_list)
        | Copy f ->
            let subproof =
              ILNode ([OfCourse f] ++ sequent, ILder_L, proof_list) in
            ILNode (sequent, ILcont_L, [subproof])
        | _ ->
            List.hd proof_list

(* [print_ill_rule ff rule] outputs the ILL rule [rule] on the formatter [ff]. *)
let print_ill_rule ff = function
  | ILAx -> print_str ff "Ax"
  | ILTensor_L -> print_str ff "Tensor_L"
  | ILTensor_R -> print_str ff "Tensor_R"
  | ILOne_L -> print_str ff "One_L"
  | ILOne_R -> print_str ff "One_R"
  | ILImpl_L -> print_str ff "Impl_L"
  | ILImpl_R -> print_str ff "Impl_R"
  | ILPlus_L -> print_str ff "Plus_L"
  | ILPlus_R_1 -> print_str ff "Plus_R_1"
  | ILPlus_R_2 -> print_str ff "Plus_R_2"
  | ILZero_L -> print_str ff "Zero_L"
  | ILWith_L_1 -> print_str ff "With_L_1"
  | ILWith_L_2 -> print_str ff "With_L_2"
  | ILWith_R -> print_str ff "With_R"
  | ILTop_R -> print_str ff "Top_R"
  | ILwk_L -> print_str ff "wk_L"
  | ILcont_L -> print_str ff "cont_L"
  | ILder_L -> print_str ff "der_L"
  | ILOfCourse_R -> print_str ff "OfCourse_R"

(* [print_ill_sequent ff seq] outputs the ILL sequent [seq] on the formatter [ff].
   *)
let print_ill_sequent ff (gamma, f) =
  fprintf ff "@[{%a |- %a@?}@]"
  (pp_print_list ~pp_sep:print_sep print_formula) gamma print_formula f

(* [print_ill_proof ff proof] outputs the ILL proof [proof] on the formatter [ff].
   *)
let rec print_ill_proof ff = function
  | ILNode (seq, r, proof_list) ->
      fprintf ff "@[(%a -> %a -> [%a])@]@?"
      print_ill_sequent seq
      print_ill_rule r
      print_ill_proof_list proof_list
  | ILNull -> ()

(* [print_ill_proof_list ff proof_list] outputs the list [proof_list] of ILL
   proofs on the formatter [ff]. *)
and print_ill_proof_list ff proof_list =
  fprintf ff "@[%a@]@?"
  (pp_print_list ~pp_sep:print_sep print_ill_proof) proof_list

(* [output_proof_ill proof filename] writes the ILL proof corresponding to the
   ILLF proof [proof] into the file [filename]. *)
let output_proof_ill proof filename =
  let oc = open_out filename in
  let ff = formatter_of_out_channel oc in
  print_ill_proof ff (illf_to_ill_proof proof);
  close_out oc
