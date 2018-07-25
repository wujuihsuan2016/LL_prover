open Formula
open Format
open Printer
open Fctns 

let rec latex_unop ff fmt f =
  if not (is_binop f) then
    fprintf ff fmt latex_formula f
  else
    fprintf ff fmt latex_formula_with_paren f

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

and latex_formula_with_paren ff formula = 
  fprintf ff "(%a)" latex_formula formula

let rec suffix = function
  | [] -> [[]]
  | hd :: tl -> 
      (hd :: tl) :: (suffix tl)

let print_sep ff () =
  fprintf ff "%s" ", "

let latex_flist ff l =
  if l = [] then fprintf ff "\\cdot"
  else
    fprintf ff "%a@?" (pp_print_list ~pp_sep:print_sep latex_formula) l
  
let map_wn = List.map (fun x -> Whynot x)  

let latex_sequent ff sequent = 
  let theta, gamma, l = get_theta sequent, get_gamma sequent, get_list sequent in
  fprintf ff "\\vdash %a@?"  
  latex_flist (map_wn (Set_formula.elements theta) @ gamma @ l)

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
            fprintf ff "\\infer1[$\parr$]{ %a }\n@?" latex_sequent sequent
        | Tensor_intro (l1, l2) ->
            let [@warning "-8"] [br1; br2] = proof_list in
            ll_proof_to_latex_one_sided ff br1;
            ll_proof_to_latex_one_sided ff br2;
            let theta_list = Set_formula.elements theta in 
            let theta_list' = ref theta_list in
            fprintf ff "\\infer2[$\otimes$]{ \\vdash %a }\n@?" 
            latex_flist (map_wn (theta_list @ theta_list) @ gamma @ l);  
            while !theta_list' <> [] do
              theta_list' := List.tl !theta_list';
              fprintf ff "\\infer1[$co$]{ \\vdash %a }\n@?" latex_flist (map_wn
              (!theta_list' @ theta_list) @ gamma @ l)
            done
        | With_intro ->
            let [@warning "-8"] [br1; br2] = proof_list in
            ll_proof_to_latex_one_sided ff br1;
            ll_proof_to_latex_one_sided ff br2;
            fprintf ff "\\infer2[$\with$]{ %a }\n@?" latex_sequent sequent
        | Plus_intro_1 ->
            ll_proof_to_latex_one_sided ff (List.hd proof_list);
            fprintf ff "\\infer1[$\oplus_1$]{ %a }\n@?" latex_sequent sequent
        | Plus_intro_2 ->
            ll_proof_to_latex_one_sided ff (List.hd proof_list);
            fprintf ff "\\infer1[$\oplus_2$]{ %a }\n@?" latex_sequent sequent
        | OfCourse_intro ->
            ll_proof_to_latex_one_sided ff (List.hd proof_list);
            fprintf ff "\\infer1[$!$]{ %a }\n@?" latex_sequent sequent
        | Whynot_intro ->
            let [@warning "-8"] (Whynot f) :: l' = l in
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
            let [@warning "-8"] [Pos x] = l in
            let theta'_list = 
              Set_formula.elements (Set_formula.remove (Neg x) theta) in 
            fprintf ff "\\infer0[$ax$]{ \\vdash %a }\n@?" latex_flist [Neg x; Pos x];
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
          fprintf ff "\\infer1[$\parr$]{ %a }\n@?" llf_latex_sequent sequent
      | Tensor_intro _ -> 
          let [@warning "-8"] [br1; br2] = proof_list in
          ll_proof_to_latex_llf ff br1;
          ll_proof_to_latex_llf ff br2;
          fprintf ff "\\infer2[$\otimes$]{ %a }\n@?" llf_latex_sequent sequent
      | With_intro -> 
          let [@warning "-8"] [br1; br2] = proof_list in
          ll_proof_to_latex_llf ff br1;
          ll_proof_to_latex_llf ff br2;
          fprintf ff "\\infer2[$\with$]{ %a }\n@?" llf_latex_sequent sequent
      | Plus_intro_1 -> 
          ll_proof_to_latex_llf ff (List.hd proof_list);
          fprintf ff "\\infer1[$\oplus_1$]{ %a }\n@?" llf_latex_sequent sequent
      | Plus_intro_2 ->
          ll_proof_to_latex_llf ff (List.hd proof_list);
          fprintf ff "\\infer1[$\oplus_2$]{ %a }\n@?" llf_latex_sequent sequent
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
          fprintf ff "\\infer1[$R_{\Uparrow}$]{ %a }\n@?" 
          llf_latex_sequent sequent
      | R_sync ->
          ll_proof_to_latex_llf ff (List.hd proof_list);
          fprintf ff "\\infer1[$R_{\Downarrow}$]{ %a }\n@?"
          llf_latex_sequent sequent 
(* ILL *)

let map_oc = List.map (fun x -> OfCourse x)

let ill_latex_sequent ff = function
  | R_focal (theta, gamma, f) ->
      fprintf ff "%a \\vdash %a@?"
      latex_flist (map_oc (Set_formula.elements theta) @ gamma)
      latex_formula f
  | L_focal (theta, gamma, f, g) -> 
      fprintf ff "%a \\vdash %a@?"
      latex_flist (map_oc (Set_formula.elements theta) @ (f :: gamma))
      latex_formula g
  | Active (theta, gamma, l, f) ->
      fprintf ff "%a \\vdash %a@?"
      latex_flist (map_oc (Set_formula.elements theta) @ l @ gamma)
      latex_formula f

let rec ill_proof_to_latex ff = function
  | INull -> ()
  | INode (sequent, rule, proof_list) ->
      let theta, gamma, formula =
        ill_get_theta sequent, ill_get_gamma sequent, ill_get_formula sequent in
      let theta_list = Set_formula.elements theta in
      match rule with
        | Tensor_L ->
            ill_proof_to_latex ff (List.hd proof_list);
            fprintf ff "\\infer1[$\otimes_L$]{ %a }\n@?"
            ill_latex_sequent sequent
        | Tensor_R (gamma1, gamma2) ->
            let [@warning "-8"] [br1; br2] = proof_list in
            ill_proof_to_latex ff br1;
            ill_proof_to_latex ff br2;
            fprintf ff "\\infer2[$\otimes_R$]{ %a \\vdash %a }\n@?"
            latex_flist (map_oc (theta_list @ theta_list) @ gamma)
            latex_formula formula;
            let suffix_theta = List.tl (suffix theta_list) in
            List.iter 
              (fun x -> 
                 fprintf ff "\\infer1[$co_L$]{ %a \\vdash %a }\n@?"
                 latex_flist (map_oc (x @ theta_list) @ gamma)
                 latex_formula formula) suffix_theta
        | Impl_L (gamma1, gamma2) ->
            let [@warning "-8"] [br1; br2] = proof_list in
            ill_proof_to_latex ff br1;
            ill_proof_to_latex ff br2;
            fprintf ff "\\infer2[$\multimap_L$]{ %a \\vdash %a}\n@?"
            latex_flist (map_oc (theta_list @ theta_list) @ gamma)
            latex_formula formula;
            let suffix_theta = List.tl (suffix theta_list) in
            List.iter 
              (fun x ->
                 fprintf ff "\\infer1[$co_L$]{ %a \\vdash %a}\n@?"
                 latex_flist (map_oc (x @ theta_list) @ gamma)
                 latex_formula formula) suffix_theta
        | Impl_R ->
            ill_proof_to_latex ff (List.hd proof_list);
            fprintf ff "\\infer1[$\multimap_R$]{ %a }\n@?"
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
                latex_flist (map_oc x)) suffix_theta
        | Init ->
            fprintf ff "\\infer0[$ax$]{ %a \\vdash %a }\n@?"
            latex_formula formula latex_formula formula;
            let suffix_theta = List.tl (List.rev (suffix (map_oc theta_list))) 
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
            let [@warning "-8"] OfCourse f = List.hd gamma in
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
            let [@warning "-8"] [br1; br2] = proof_list in
            ill_proof_to_latex ff br1;
            ill_proof_to_latex ff br2;
            fprintf ff "\\infer2[$\with_R$]{ %a }\n@?" 
            ill_latex_sequent sequent
        | With_L_1 ->
            ill_proof_to_latex ff (List.hd proof_list);
            fprintf ff "\\infer1[$\with_{L_1}$]{ %a }\n@?" 
            ill_latex_sequent sequent
        | With_L_2 ->
            ill_proof_to_latex ff (List.hd proof_list);
            fprintf ff "\\infer1[$\with_{L_2}$]{ %a }\n@?" 
            ill_latex_sequent sequent
        | Plus_L ->
            let [@warning "-8"] [br1; br2] = proof_list in
            ill_proof_to_latex ff br1;
            ill_proof_to_latex ff br2;
            fprintf ff "\\infer2[$\oplus_L$]{ %a }\n@?" 
            ill_latex_sequent sequent
        | Plus_R_1 ->
            ill_proof_to_latex ff (List.hd proof_list);
            fprintf ff "\\infer1[$\oplus_{R_1}$]{ %a }\n@?" 
            ill_latex_sequent sequent 
        | Plus_R_2 ->
            ill_proof_to_latex ff (List.hd proof_list);
            fprintf ff "\\infer1[$\oplus_{R_2}$]{ %a }\n@?" 
            ill_latex_sequent sequent
        | Copy f ->
            ill_proof_to_latex ff (List.hd proof_list);
            fprintf ff "\\infer1[$!_L$]{ %a \\vdash %a}\n@?"
            latex_flist (map_oc theta_list @ (OfCourse f :: gamma)) 
            latex_formula formula;
            fprintf ff "\\infer1[$co_L$]{ %a }\n@?" ill_latex_sequent sequent
        | _ ->
            ill_proof_to_latex ff (List.hd proof_list)         

(* ILLF *)
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

let rec ill_proof_to_latex_illf ff = function
  | INull -> ()
  | INode (sequent, rule, proof_list) -> match rule with
      | Tensor_L ->
          ill_proof_to_latex_illf ff (List.hd proof_list);
          fprintf ff "\\infer1[$\otimes L$]{ %a }\n@?" illf_latex_sequent sequent
      | Tensor_R _ ->
          let [@warning "-8"] [br1; br2] = proof_list in
          ill_proof_to_latex_illf ff br1;
          ill_proof_to_latex_illf ff br2;
          fprintf ff "\\infer2[$\otimes R$]{ %a }\n@?" illf_latex_sequent sequent
      | Impl_L _ ->
          let [@warning "-8"] [br1; br2] = proof_list in
          ill_proof_to_latex_illf ff br1;
          ill_proof_to_latex_illf ff br2;
          fprintf ff "\\infer2[$\multimap L$]{ %a }\n@?" illf_latex_sequent sequent
      | Impl_R ->
          ill_proof_to_latex_illf ff (List.hd proof_list);
          fprintf ff "\\infer1[$\multimap R$]{ %a }\n@?" illf_latex_sequent sequent
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
          fprintf ff "\\infer0[$\top R$]{ %a }\n@?" illf_latex_sequent sequent
      | OfCourse_L ->
          ill_proof_to_latex_illf ff (List.hd proof_list);
          fprintf ff "\\infer1[$! R$]{ %a }\n@?" illf_latex_sequent sequent 
      | OfCourse_R ->
          ill_proof_to_latex_illf ff (List.hd proof_list);
          fprintf ff "\\infer1[$! L$]{ %a }\n@?" illf_latex_sequent sequent
      | With_R ->
          let [@warning "-8"] [br1; br2] = proof_list in
          ill_proof_to_latex_illf ff br1;
          ill_proof_to_latex_illf ff br2;
          fprintf ff "\\infer2[$\with R$]{ %a }\n@?" illf_latex_sequent sequent
      | With_L_1 ->
          ill_proof_to_latex_illf ff (List.hd proof_list);
          fprintf ff "\\infer1[$\with L_1$]{ %a }\n@?" 
          illf_latex_sequent sequent
      | With_L_2 ->
          ill_proof_to_latex_illf ff (List.hd proof_list);
          fprintf ff "\\infer1[$\with L_2$]{ %a }\n@?"
          illf_latex_sequent sequent
      | Plus_L ->
          let [@warning "-8"] [br1; br2] = proof_list in
          ill_proof_to_latex_illf ff br1;
          ill_proof_to_latex_illf ff br2;
          fprintf ff "\\infer2[$\oplus L$]{ %a }\n@?" 
          illf_latex_sequent sequent
      | Plus_R_1 ->
          ill_proof_to_latex_illf ff (List.hd proof_list);
          fprintf ff "\\infer1[$\oplus R_1$]{ %a }\n@?"
          illf_latex_sequent sequent
      | Plus_R_2 ->
          ill_proof_to_latex_illf ff (List.hd proof_list);
          fprintf ff "\\infer1[$\oplus R_2$]{ %a }\n@?"
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
  let dir, base = Filename.dirname filename, Filename.basename filename in 
  let latex_file = "latex_export/ll/" ^ dir ^ "/proof" ^ base ^ ".tex" in
  let oc = open_out latex_file in
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
  let dir, base = Filename.dirname filename, Filename.basename filename in 
  let latex_file = "latex_export/ll/" ^ dir ^ "/proof" ^ base ^ "_foc.tex" in
  let oc = open_out latex_file in
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
  let dir, base = Filename.dirname filename, Filename.basename filename in
  let latex_file = "latex_export/ill/" ^ dir ^ "/proof" ^ base ^ ".tex" in
  let oc = open_out latex_file in
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
  let dir, base = Filename.dirname filename, Filename.basename filename in
  let latex_file = "latex_export/ill/" ^ dir ^ "/proof" ^ base ^ "_foc.tex" in
  let oc = open_out latex_file in
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
