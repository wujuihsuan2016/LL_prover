(*** Export to LaTeX ***)

open Formula
open Format
open Printer
open Fctns 

(* [latex_unop ff fmt f] formats the formula [f] according to the format
   string [fmt] and outputs the resulting string on the formatter [ff].
   This function is used to print [op f] where [op] is a unary connective, by
   setting [fmt] = "[op] %a". *)
let rec latex_unop ff fmt f =
  if not (is_binop f) then
    fprintf ff fmt latex_formula f
  else
    fprintf ff fmt latex_formula_with_paren f

(* [latex_binop ff fmt f g] formats the formula [f] and [g] according to the
   format string [fmt] and outputs the resulting string on the formatter [ff].
   This function is used to print [op (f, g)] where [op] is a binary connective,
   by setting [fmt] = "%a [op] %a" *)
and latex_binop ff fmt f g =
  if not (is_binop f) then
    if not (is_binop g) then
      fprintf ff fmt latex_formula f latex_formula g
    else
      fprintf ff fmt latex_formula f latex_formula_with_paren g
  else
    if not (is_binop g) then
      fprintf ff fmt latex_formula_with_paren f latex_formula g
    else
      fprintf ff fmt latex_formula_with_paren f latex_formula_with_paren g

(* [latex_formula ff f] outputs the latex-code formula [f] on the formatter
   [ff]. *)
and latex_formula ff = function 
  | Pos s -> print_str ff s
  | Neg s -> fprintf ff "%s^{\\perp}@?" s
  | One -> print_str ff "1"
  | Zero -> print_str ff "0"
  | Top -> print_str ff "\\top"
  | Bottom -> fprintf ff "\\bot"
  | OfCourse f -> latex_unop ff " \\oc %a@?" f
  | Whynot f -> latex_unop ff "\\wn %a@?" f
  | Tensor (f, g) -> 
      latex_binop ff "%a \\otimes %a@?" f g
  | Plus (f, g) -> 
      latex_binop ff "%a \\oplus %a@?" f g
  | With (f, g) -> 
      latex_binop ff "%a \\with %a@?" f g
  | Par (f, g) -> 
      latex_binop ff "%a \\parr %a@?" f g
  | Impl (f, g) -> 
      latex_binop ff "%a \\multimap %a@?" f g

(* [latex_formula_with_paren ff f] outputs the latex code of the formula [f]
   enclosed in parentheses on the formatter [ff]. *)
and latex_formula_with_paren ff formula = 
  fprintf ff "(%a)" latex_formula formula

(* [print_sep ff ()] outputs the separator (comma) on the formatter [ff]. *)
let print_sep ff () =
  fprintf ff "%s" ", "

(* [latex_flist ff l] outputs the latex code of the list [l] of formulas
   separated by commas on the formatter [ff]. *)
let latex_flist ff l =
  if l = [] then fprintf ff "\\cdot"
  else
    fprintf ff "%a@?" (pp_print_list ~pp_sep:print_sep latex_formula) l

(* [latex_sequent ff sequent] outputs the latex code of the one-sided sequent
   [sequent] on the formatter [ff]. *)
let latex_sequent ff sequent = 
  let theta, gamma, l = get_theta sequent, get_gamma sequent, get_list sequent in
  fprintf ff "\\vdash %a@?"  
  latex_flist (map_wn (Set_formula.elements theta) @ gamma @ l)

(* [latex_sequent_2 ff sequent] outputs the latex code of the two-sided sequent
   [sequent] on the formatter [ff]. *)
let latex_sequent_2 ff (l1, l2) = 
  fprintf ff "%a \\vdash %a@?" latex_flist l1 latex_flist l2

let print_latex_sequent ff sequent =
  print_str_line ff "\\documentclass[a4]{article}";
  print_str_line ff "\\usepackage{amsmath}";
  print_str_line ff "\\usepackage{ebproof}";
  print_str_line ff "\\usepackage{cmll}";
  print_str_line ff "\\usepackage{txfonts}";
  print_str_line ff "\\usepackage[a4paper, margin = 1.5cm]{geometry}";
  print_str_line ff "\\usepackage{graphics}";
  print_str_line ff "\\begin{document}";
  print_str_line ff "\\center";
  print_str_line ff "\\resizebox{\\textwidth}{!}{";
  Format.fprintf ff "$%a$}\n@?" latex_sequent_2 sequent;
  print_str_line ff "\\end{document}"

(** LL **)

(* [ll_proof_to_latex_one_sided ff proof] outputs the latex code of the LL
   proof corresponding to the LLF proof [proof] on the formatter [ff]. *)
let rec ll_proof_to_latex_one_sided ff = function
  | Null -> ()
  | Node (sequent, rule, proof_list) ->
      let theta, gamma, l =
        get_theta sequent, get_gamma sequent, get_list sequent in
      match rule with
        | Top_intro ->
            fprintf ff "\\infer0[$\\top$]{ %a }\n@?" latex_sequent sequent
        | Bottom_intro ->
            ll_proof_to_latex_one_sided ff (List.hd proof_list);
            fprintf ff "\\infer1[$\\bot$]{ %a }\n@?" latex_sequent sequent
        | One_intro ->
            print_str_line ff "\\infer0[$1$]{ \\vdash 1 }\n@?";
            let suffix_theta = 
              List.tl (List.rev (suffix (Set_formula.elements theta))) in
            List.iter 
              (fun x -> 
                 fprintf ff "\\infer1[$wk$]{ \\vdash %a, 1 }\n@?" latex_flist
                 (map_wn x)) 
              suffix_theta
        | Par_intro ->
            ll_proof_to_latex_one_sided ff (List.hd proof_list);
            fprintf ff "\\infer1[$\\parr$]{ %a }\n@?" latex_sequent sequent
        | Tensor_intro (l1, l2) ->
            List.iter (ll_proof_to_latex_one_sided ff) proof_list;
            let theta_list = Set_formula.elements theta in 
            let theta_list' = ref theta_list in
            fprintf ff "\\infer2[$\\otimes$]{ \\vdash %a }\n@?"
            latex_flist (map_wn (theta_list @ theta_list) @ gamma @ l);  
            while !theta_list' <> [] do
              theta_list' := List.tl !theta_list';
              fprintf ff "\\infer1[$co$]{ \\vdash %a }\n@?" latex_flist
              (map_wn (!theta_list' @ theta_list) @ gamma @ l)
            done
        | With_intro ->
            List.iter (ll_proof_to_latex_one_sided ff) proof_list;
            fprintf ff "\\infer2[$\\with$]{ %a }\n@?" latex_sequent sequent
        | Plus_intro_1 ->
            ll_proof_to_latex_one_sided ff (List.hd proof_list);
            fprintf ff "\\infer1[$\\oplus_1$]{ %a }\n@?" latex_sequent sequent
        | Plus_intro_2 ->
            ll_proof_to_latex_one_sided ff (List.hd proof_list);
            fprintf ff "\\infer1[$\\oplus_2$]{ %a }\n@?" latex_sequent sequent
        | OfCourse_intro ->
            ll_proof_to_latex_one_sided ff (List.hd proof_list);
            fprintf ff "\\infer1[$!$]{ %a }\n@?" latex_sequent sequent
        | Whynot_intro ->
            let f, l' =
              match l with (Whynot f) :: l' -> (f, l') | _ -> assert false in
            if Set_formula.mem f theta then begin
              ll_proof_to_latex_one_sided ff (List.hd proof_list);
              fprintf ff "\\infer1[$wk$]{ %a }\n@?" latex_sequent sequent
              end
            else
              ll_proof_to_latex_one_sided ff (List.hd proof_list)
        | I1 ->
            if Set_formula.is_empty theta then
              fprintf ff "\\infer0[$ax$]{ %a }\n@?" latex_sequent sequent
            else
              fprintf ff "\\infer0[$ax$]{ \\vdash %a }\n@?" latex_flist (gamma @ l);
              let suffix_theta = 
                List.tl (List.rev (suffix (Set_formula.elements theta))) in
              List.iter 
                (fun x -> 
                  fprintf ff "\\infer1[$wk$]{ \\vdash %a }\n@?" latex_flist
                  (map_wn x @ gamma @ l)) 
                suffix_theta
        | I2 ->
            let x = match l with [Pos x] -> x | _ -> assert false in
            let theta'_list = 
              Set_formula.elements (Set_formula.remove (Neg x) theta) in 
            fprintf ff "\\infer0[$ax$]{ \\vdash %a }\n@?"
            latex_flist [Neg x; Pos x];
            fprintf ff "\\infer1[$de$]{ \\vdash %a }\n@?" 
            latex_flist [Whynot (Neg x); Pos x];
            let suffix_theta = 
              List.tl (List.rev (suffix theta'_list)) in
            List.iter 
              (fun y -> 
                 fprintf ff "\\infer1[$wk$]{ \\vdash %a }\n@?" latex_flist
                 (map_wn y @
                 [Whynot (Neg x); Pos x])) 
              suffix_theta
        | D1 _ ->
            ll_proof_to_latex_one_sided ff (List.hd proof_list)
        | D2 f ->
            ll_proof_to_latex_one_sided ff (List.hd proof_list);
            fprintf ff "\\infer1[$de$]{ %a }\n@?" latex_sequent 
            (Sync (theta, gamma, Whynot f));
            fprintf ff "\\infer1[$co$]{ %a }\n@?" latex_sequent sequent;
        | R_async | R_sync -> 
            ll_proof_to_latex_one_sided ff (List.hd proof_list)

(* LLF *)

(* [llf_latex_sequent ff sequent] outputs the latex code of the LLF sequent
   [sequent] on the formatter [ff]. *)
let llf_latex_sequent ff = function
  | Async (theta, gamma, l) -> 
      fprintf ff "\\vdash %a : %a \\Uparrow %a@?"
      latex_flist (Set_formula.elements theta)
      latex_flist gamma
      latex_flist l
  | Sync (theta, gamma, f) ->
      fprintf ff "\\vdash %a : %a \\Downarrow %a@?"
      latex_flist (Set_formula.elements theta)
      latex_flist gamma
      latex_formula f

(* [ll_proof_to_latex_llf ff proof] outputs the latex code of the LLF proof
   [proof]. *)
let rec ll_proof_to_latex_llf ff = function
  | Null -> ()
  | Node (sequent, rule, proof_list) -> match rule with
      | Top_intro -> 
          fprintf ff "\\infer0[$\top$]{ %a }\n@?" llf_latex_sequent sequent
      | Bottom_intro -> 
          ll_proof_to_latex_llf ff (List.hd proof_list);
          fprintf ff "\\infer1[$\bot$]{ %a }\n@?" llf_latex_sequent sequent
      | One_intro -> 
          fprintf ff "\\infer0[$1$]{ %a }\n@?" llf_latex_sequent sequent
      | Par_intro -> 
          ll_proof_to_latex_llf ff (List.hd proof_list);
          fprintf ff "\\infer1[$\\parr$]{ %a }\n@?" llf_latex_sequent sequent
      | Tensor_intro _ -> 
          List.iter (ll_proof_to_latex_llf ff) proof_list;
          fprintf ff "\\infer2[$\\otimes$]{ %a }\n@?" llf_latex_sequent sequent
      | With_intro -> 
          List.iter (ll_proof_to_latex_llf ff) proof_list;
          fprintf ff "\\infer2[$\\with$]{ %a }\n@?" llf_latex_sequent sequent
      | Plus_intro_1 -> 
          ll_proof_to_latex_llf ff (List.hd proof_list);
          fprintf ff "\\infer1[$\\oplus_1$]{ %a }\n@?" llf_latex_sequent sequent
      | Plus_intro_2 ->
          ll_proof_to_latex_llf ff (List.hd proof_list);
          fprintf ff "\\infer1[$\\oplus_2$]{ %a }\n@?" llf_latex_sequent sequent
      | OfCourse_intro ->
          ll_proof_to_latex_llf ff (List.hd proof_list);
          fprintf ff "\\infer1[$!$]{ %a }\n@?" llf_latex_sequent sequent
      | Whynot_intro ->
          ll_proof_to_latex_llf ff (List.hd proof_list);
          fprintf ff "\\infer1[$?$]{ %a }\n@?" llf_latex_sequent sequent 
      | I1 ->
          fprintf ff "\\infer0[$I_1$]{ %a }\n@?" llf_latex_sequent sequent
      | I2 ->
          fprintf ff "\\infer0[$I_2$]{ %a }\n@?" llf_latex_sequent sequent
      | D1 _ ->
          ll_proof_to_latex_llf ff (List.hd proof_list);
          fprintf ff "\\infer1[$D_1$]{ %a }\n@?" llf_latex_sequent sequent
      | D2 _ ->
          ll_proof_to_latex_llf ff (List.hd proof_list);
          fprintf ff "\\infer1[$D_2$]{ %a }\n@?" llf_latex_sequent sequent
      | R_async ->
          ll_proof_to_latex_llf ff (List.hd proof_list);
          fprintf ff "\\infer1[$R_{\\Uparrow}$]{ %a }\n@?"
          llf_latex_sequent sequent
      | R_sync ->
          ll_proof_to_latex_llf ff (List.hd proof_list);
          fprintf ff "\\infer1[$R_{\\Downarrow}$]{ %a }\n@?"
          llf_latex_sequent sequent 

(** ILL **)

(* [ill_latex_sequent ff sequent] outputs the latex code of the ILL sequent
   corresponding to the ILLF sequent [sequent]. *)
let ill_latex_sequent ff = function
  | R_focal (theta, gamma, f) ->
      fprintf ff "%a \\vdash %a@?"
      latex_flist (map_oc theta @ gamma)
      latex_formula f
  | L_focal (theta, gamma, f, g) -> 
      fprintf ff "%a \\vdash %a@?"
      latex_flist (map_oc theta @ (f :: gamma))
      latex_formula g
  | Active (theta, gamma, l, f) ->
      fprintf ff "%a \\vdash %a@?"
      latex_flist (map_oc theta @ l @ gamma)
      latex_formula f

(* [print_ill_latex_sequent ff sequent] outputs the latex code that can be
   compiled to a single file of the ILL sequent corresponding to the ILLF
   sequent [sequent]. *)
let print_ill_latex_sequent ff sequent = 
  print_str_line ff "\\documentclass[a4]{article}";
  print_str_line ff "\\usepackage{amsmath}";
  print_str_line ff "\\usepackage{ebproof}";
  print_str_line ff "\\usepackage{cmll}";
  print_str_line ff "\\usepackage{txfonts}";
  print_str_line ff "\\usepackage[a4paper, margin = 1.5cm]{geometry}";
  print_str_line ff "\\usepackage{graphics}";
  print_str_line ff "\\begin{document}";
  print_str_line ff "\\center";
  print_str_line ff "\\resizebox{\\textwidth}{!}{";
  Format.fprintf ff "$%a$}\n@?" ill_latex_sequent sequent;
  print_str_line ff "\\end{document}"

(* [ill_proof_to_latex ff proof] ouptuts the latex code of the ILL proof
   corresponding to the ILLF proof [proof]. *)
let rec ill_proof_to_latex ff = function
  | INull -> ()
  | INode (sequent, rule, proof_list) ->
      let theta, gamma, formula =
        ill_get_theta sequent, ill_get_gamma sequent, ill_get_formula sequent in
      let theta_list = Set_formula.elements theta in
      match rule with
        | Tensor_L ->
            ill_proof_to_latex ff (List.hd proof_list);
            fprintf ff "\\infer1[$\\otimes_L$]{ %a }\n@?"
            ill_latex_sequent sequent
        | Tensor_R (gamma1, gamma2) ->
            List.iter (ill_proof_to_latex ff) proof_list;
            fprintf ff "\\infer2[$\\otimes_R$]{ %a \\vdash %a }\n@?"
            latex_flist (map_oc' (theta_list @ theta_list) @ gamma)
            latex_formula formula;
            let suffix_theta = List.tl (suffix theta_list) in
            List.iter 
              (fun x -> 
                 fprintf ff "\\infer1[$co_L$]{ %a \\vdash %a }\n@?"
                 latex_flist (map_oc' (x @ theta_list) @ gamma)
                 latex_formula formula) suffix_theta
        | Impl_L (gamma1, gamma2) ->
            List.iter (ill_proof_to_latex ff) proof_list;
            fprintf ff "\\infer2[$\\multimap_L$]{ %a \\vdash %a}\n@?"
            latex_flist (map_oc' (theta_list @ theta_list) @ gamma)
            latex_formula formula;
            let suffix_theta = List.tl (suffix theta_list) in
            List.iter 
              (fun x ->
                 fprintf ff "\\infer1[$co_L$]{ %a \\vdash %a}\n@?"
                 latex_flist (map_oc' (x @ theta_list) @ gamma)
                 latex_formula formula) suffix_theta
        | Impl_R ->
            ill_proof_to_latex ff (List.hd proof_list);
            fprintf ff "\\infer1[$\\multimap_R$]{ %a }\n@?"
            ill_latex_sequent sequent
        | One_L ->
            ill_proof_to_latex ff (List.hd proof_list);
            fprintf ff "\\infer1[$1_L$]{ %a }\n@?"
            ill_latex_sequent sequent
        | One_R ->
            fprintf ff "\\infer0[$1_R$]{ \\vdash %a }\n@?"
            latex_formula One;
            let suffix_theta = List.tl (List.rev (suffix theta_list)) in
            List.iter 
              (fun x ->
                fprintf ff "\\infer1[$wk_L$]{ %a \\vdash 1}\n@?"
                latex_flist (map_oc' x)) suffix_theta
        | Init ->
            fprintf ff "\\infer0[$ax$]{ %a \\vdash %a }\n@?"
            latex_formula formula latex_formula formula;
            let suffix_theta = List.tl (List.rev (suffix (map_oc' theta_list)))
            in
            List.iter 
              (fun x ->
                 fprintf ff "\\infer1[$wk_L$]{ %a \\vdash %a }\n@?"
                 latex_flist (formula :: x) latex_formula formula) suffix_theta
        | Top_R ->
            fprintf ff "\\infer0[$\\top_R$]{ %a }\n@?" ill_latex_sequent sequent
        | Zero_L ->
            fprintf ff "\\infer0[$0_L$]{ %a }\n@?" ill_latex_sequent sequent
        | OfCourse_L ->
            let f = match List.hd gamma with OfCourse f -> f | _ -> assert false
            in
            if Set_formula.mem f theta then begin 
              ill_proof_to_latex ff (List.hd proof_list);
              fprintf ff "\\infer1[$wk_L$]{ %a }\n@?" ill_latex_sequent sequent
            end
            else
              ill_proof_to_latex ff (List.hd proof_list);
        | OfCourse_R ->
            ill_proof_to_latex ff (List.hd proof_list);
            fprintf ff "\\infer1[$!_R$]{ %a }\n@?" ill_latex_sequent sequent
        | With_R ->
            List.iter (ill_proof_to_latex ff) proof_list;
            fprintf ff "\\infer2[$\\with_R$]{ %a \\vdash %a }\n@?"
            latex_flist (map_oc' (theta_list @ theta_list) @ gamma)
            latex_formula formula
        | With_L_1 ->
            ill_proof_to_latex ff (List.hd proof_list);
            fprintf ff "\\infer1[$\\with_{L_1}$]{ %a }\n@?"
            ill_latex_sequent sequent
        | With_L_2 ->
            ill_proof_to_latex ff (List.hd proof_list);
            fprintf ff "\\infer1[$\\with_{L_2}$]{ %a }\n@?"
            ill_latex_sequent sequent
        | Plus_L ->
            List.iter (ill_proof_to_latex ff) proof_list;
            fprintf ff "\\infer2[$\\oplus_L$]{ %a }\n@?"
            ill_latex_sequent sequent
        | Plus_R_1 ->
            ill_proof_to_latex ff (List.hd proof_list);
            fprintf ff "\\infer1[$\\oplus_{R_1}$]{ %a }\n@?"
            ill_latex_sequent sequent 
        | Plus_R_2 ->
            ill_proof_to_latex ff (List.hd proof_list);
            fprintf ff "\\infer1[$\\oplus_{R_2}$]{ %a }\n@?"
            ill_latex_sequent sequent
        | Copy f ->
            ill_proof_to_latex ff (List.hd proof_list);
            fprintf ff "\\infer1[$!_L$]{ %a \\vdash %a}\n@?"
            latex_flist (map_oc' theta_list @ (OfCourse f :: gamma))
            latex_formula formula;
            fprintf ff "\\infer1[$co_L$]{ %a }\n@?" ill_latex_sequent sequent
        | _ ->
            ill_proof_to_latex ff (List.hd proof_list)         

(** ILLF **)

(* [illf_latex_sequent ff sequent] outputs the latex code of the ILLF sequent
   [sequent] on the formatter [ff]. *)
let illf_latex_sequent ff = function
  | R_focal (theta, gamma, f) -> 
      fprintf ff "%a ; %a \\gg %a"
      latex_flist (Set_formula.elements theta)
      latex_flist gamma
      latex_formula f
  | L_focal (theta, gamma, f, g) ->
      fprintf ff "%a ; %a ; %a \\ll %a"
      latex_flist (Set_formula.elements theta)
      latex_flist gamma
      latex_formula f 
      latex_formula g
  | Active (theta, gamma, omega, f) ->
      fprintf ff "%a ; %a ; %a \\Longrightarrow %a"
      latex_flist (Set_formula.elements theta)
      latex_flist gamma
      latex_flist omega
      latex_formula f

(* [ill_proof_to_latex_illf ff proof] outputs the latex code of the ILLF proof
   [proof] on the formatter [ff]. *)
let rec ill_proof_to_latex_illf ff = function
  | INull -> ()
  | INode (sequent, rule, proof_list) -> match rule with
      | Tensor_L ->
          ill_proof_to_latex_illf ff (List.hd proof_list);
          fprintf ff "\\infer1[$\\otimes L$]{ %a }\n@?" illf_latex_sequent
          sequent
      | Tensor_R _ ->
          List.iter (ill_proof_to_latex_illf ff) proof_list;
          fprintf ff "\\infer2[$\\otimes R$]{ %a }\n@?" illf_latex_sequent
          sequent
      | Impl_L _ ->
          List.iter (ill_proof_to_latex_illf ff) proof_list;
          fprintf ff "\\infer2[$\\multimap L$]{ %a }\n@?" illf_latex_sequent
          sequent
      | Impl_R ->
          ill_proof_to_latex_illf ff (List.hd proof_list);
          fprintf ff "\\infer1[$\\multimap R$]{ %a }\n@?" illf_latex_sequent
          sequent
      | One_L ->
          ill_proof_to_latex_illf ff (List.hd proof_list);
          fprintf ff "\\infer1[$1 L$]{ %a }\n@?" illf_latex_sequent sequent
      | One_R ->
          fprintf ff "\\infer0[$1 R$]{ %a }\n@?" illf_latex_sequent sequent 
      | Zero_L ->
          fprintf ff "\\infer0[$0 R$]{ %a }\n@?" illf_latex_sequent sequent
      | Init ->
          fprintf ff "\\infer0[$init$]{ %a }\n@?" illf_latex_sequent sequent
      | Top_R ->
          fprintf ff "\\infer0[$\\top R$]{ %a }\n@?" illf_latex_sequent sequent
      | OfCourse_L ->
          ill_proof_to_latex_illf ff (List.hd proof_list);
          fprintf ff "\\infer1[$! R$]{ %a }\n@?" illf_latex_sequent sequent 
      | OfCourse_R ->
          ill_proof_to_latex_illf ff (List.hd proof_list);
          fprintf ff "\\infer1[$! L$]{ %a }\n@?" illf_latex_sequent sequent
      | With_R ->
          List.iter (ill_proof_to_latex_illf ff) proof_list;
          fprintf ff "\\infer2[$\\with R$]{ %a }\n@?" illf_latex_sequent sequent
      | With_L_1 ->
          ill_proof_to_latex_illf ff (List.hd proof_list);
          fprintf ff "\\infer1[$\\with L_1$]{ %a }\n@?"
          illf_latex_sequent sequent
      | With_L_2 ->
          ill_proof_to_latex_illf ff (List.hd proof_list);
          fprintf ff "\\infer1[$\\with L_2$]{ %a }\n@?"
          illf_latex_sequent sequent
      | Plus_L ->
          List.iter (ill_proof_to_latex_illf ff) proof_list;
          fprintf ff "\\infer2[$\\oplus L$]{ %a }\n@?"
          illf_latex_sequent sequent
      | Plus_R_1 ->
          ill_proof_to_latex_illf ff (List.hd proof_list);
          fprintf ff "\\infer1[$\\oplus R_1$]{ %a }\n@?"
          illf_latex_sequent sequent
      | Plus_R_2 ->
          ill_proof_to_latex_illf ff (List.hd proof_list);
          fprintf ff "\\infer1[$\\oplus R_2$]{ %a }\n@?"
          illf_latex_sequent sequent
      | Lf ->
          ill_proof_to_latex_illf ff (List.hd proof_list);
          fprintf ff "\\infer1[$lf$]{ %a }\n@?" illf_latex_sequent sequent
      | Copy _ ->
          ill_proof_to_latex_illf ff (List.hd proof_list);
          fprintf ff "\\infer1[$copy$]{ %a }\n@?" illf_latex_sequent sequent
      | Rf ->
          ill_proof_to_latex_illf ff (List.hd proof_list);
          fprintf ff "\\infer1[$rf$]{ %a }\n@?" illf_latex_sequent sequent
      | Lb ->
          ill_proof_to_latex_illf ff (List.hd proof_list);
          fprintf ff "\\infer1[$lb$]{ %a }\n@?" illf_latex_sequent sequent
      | Rb ->
          ill_proof_to_latex_illf ff (List.hd proof_list);
          fprintf ff "\\infer1[$rb$]{ %a }\n@?" illf_latex_sequent sequent
      | Rb_ ->
          ill_proof_to_latex_illf ff (List.hd proof_list);
          fprintf ff "\\infer1[$rb'$]{ %a }\n@?" illf_latex_sequent sequent
      | Act ->
          ill_proof_to_latex_illf ff (List.hd proof_list);
          fprintf ff "\\infer1[$act$]{ %a }\n@?" illf_latex_sequent sequent

let output_proof_ll proof filename =
  let oc = open_out filename in
  let ff = formatter_of_out_channel oc in
  print_str_line ff "\\documentclass[a4]{article}";
  print_str_line ff "\\usepackage{amsmath}";
  print_str_line ff "\\usepackage{ebproof}";
  print_str_line ff "\\usepackage{cmll}";
  print_str_line ff "\\usepackage{txfonts}";
  print_str_line ff "\\usepackage[a4paper, margin = 1.5cm]{geometry}";
  print_str_line ff "\\usepackage{graphics}";
  print_str_line ff "\\begin{document}";
  print_str_line ff "\\center";
  print_str_line ff "\\resizebox{\\textwidth}{!}{";
  print_str_line ff "\\begin{prooftree}";
  ll_proof_to_latex_one_sided ff proof;
  print_str_line ff "\\end{prooftree}}";
  print_str_line ff "\\end{document}";
  close_out oc

let output_proof_llf proof filename =
  let oc = open_out filename in
  let ff = formatter_of_out_channel oc in
  print_str_line ff "\\documentclass[a4]{article}";
  print_str_line ff "\\usepackage{amsmath}";
  print_str_line ff "\\usepackage{ebproof}";
  print_str_line ff "\\usepackage{cmll}";
  print_str_line ff "\\usepackage{txfonts}";
  print_str_line ff "\\usepackage[a4paper, margin = 1.5cm]{geometry}";
  print_str_line ff "\\usepackage{graphics}";
  print_str_line ff "\\begin{document}";
  print_str_line ff "\\center";
  print_str_line ff "\\resizebox{\\textwidth}{!}{";
  print_str_line ff "\\begin{prooftree}";
  ll_proof_to_latex_llf ff proof;
  print_str_line ff "\\end{prooftree}}";
  print_str_line ff "\\end{document}";
  close_out oc

let output_proof_ill proof filename =
  let oc = open_out filename in
  let ff = formatter_of_out_channel oc in
  print_str_line ff "\\documentclass[a4]{article}";
  print_str_line ff "\\usepackage{amsmath}";
  print_str_line ff "\\usepackage{ebproof}";
  print_str_line ff "\\usepackage{cmll}";
  print_str_line ff "\\usepackage{txfonts}";
  print_str_line ff "\\usepackage[a4paper, margin = 1.5cm]{geometry}";
  print_str_line ff "\\usepackage{graphics}";
  print_str_line ff "\\begin{document}";
  print_str_line ff "\\center";
  print_str_line ff "\\resizebox{\\textwidth}{!}{";
  print_str_line ff "\\begin{prooftree}";
  ill_proof_to_latex ff proof;
  print_str_line ff "\\end{prooftree}}";
  print_str_line ff "\\end{document}";
  close_out oc

let output_proof_illf proof filename =
  let oc = open_out filename in
  let ff = formatter_of_out_channel oc in
  print_str_line ff "\\documentclass[a4]{article}";
  print_str_line ff "\\usepackage{amsmath}";
  print_str_line ff "\\usepackage{ebproof}";
  print_str_line ff "\\usepackage{cmll}";
  print_str_line ff "\\usepackage{txfonts}";
  print_str_line ff "\\usepackage[a4paper, margin = 1.5cm]{geometry}";
  print_str_line ff "\\usepackage{graphics}";
  print_str_line ff "\\begin{document}";
  print_str_line ff "\\center";
  print_str_line ff "\\resizebox{\\textwidth}{!}{";
  print_str_line ff "\\begin{prooftree}";
  ill_proof_to_latex_illf ff proof;
  print_str_line ff "\\end{prooftree}}";
  print_str_line ff "\\end{document}";
  close_out oc
