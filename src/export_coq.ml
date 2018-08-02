open Formula
open Printer
open Format
open Fctns

type mapwn = MapWn of formula list

type yalla_rule = 
  | Ax_r 
  | One_r
  | Top_r
  | Bot_r
  | Tens_r 
  | Parr_r
  | Plus_r1
  | Plus_r2
  | With_r
  | Oc_r
  | De_r
  | Wk_r
  | Wk_list_r
  | Co_r
  | Co_std_list_r
  | Rewrite_tens of formula * (formula list * mapwn) * (formula list * mapwn)
  | Rewrite_co_std_list of mapwn * formula list
  | Rewrite_one of mapwn 
  | Rewrite_wk_list of mapwn * formula list
  | Rewrite_ax of formula * formula
  | Rewrite of formula list * mapwn 
  | Ax_exp
  | Seq of yalla_rule list
  | Rot

let map_wn = List.map (fun x -> Whynot x) 

let print_mwn ff (MapWn l) = 
  fprintf ff "map wn %a@?" print_yalla_flist l  

let print_yalla_rule ff = function
  | Ax_r -> print_str_line ff "apply ax_r."
  | One_r -> print_str_line ff "apply one_r."
  | Bot_r -> print_str_line ff "apply bot_r."
  | Top_r -> print_str_line ff "apply top_r."
  | Tens_r -> print_str_line ff "apply tens_r."
  | Parr_r -> print_str_line ff "apply parr_r."
  | Plus_r1 -> print_str_line ff "apply plus_r1."
  | Plus_r2 -> print_str_line ff "apply plus_r2."
  | With_r -> print_str_line ff "apply with_r."
  | Oc_r -> print_str_line ff "apply oc_r."
  | De_r -> print_str_line ff "apply de_r."
  | Wk_r -> print_str_line ff "apply wk_r."
  | Wk_list_r -> print_str_line ff "apply wk_list_r."
  | Co_r -> print_str_line ff "apply co_r."
  | Co_std_list_r -> print_str_line ff "apply co_std_list_r."
  | Rewrite_tens (f, (l1, mwn1), (l2, mwn2)) -> 
      fprintf ff "ex_solve (%a :: (%a ++ %a) ++ (%a ++ %a)).\n@?" 
      print_yalla_formula f
      print_yalla_flist l1 print_mwn mwn1
      print_yalla_flist l2 print_mwn mwn2
  | Rewrite_co_std_list (mwn, l) ->
      fprintf ff "ex_solve (%a ++ %a).\n@?" 
      print_mwn mwn print_yalla_flist l
  | Rewrite_one mwn ->
      fprintf ff "ex_solve (%a ++ [one]).\n@?" print_mwn mwn
  | Rewrite_wk_list (mwn, l) -> 
      fprintf ff "ex_solve (%a ++ %a).\n@?" print_mwn mwn print_yalla_flist l
  | Rewrite_ax (f, g) ->
      fprintf ff "ex_solve ([%a ; %a]).\n@?" 
      print_yalla_formula f print_yalla_formula g
  | Rewrite (l, mwn) ->
      fprintf ff "ex_solve (%a ++ %a).\n@?" print_yalla_flist l print_mwn mwn
  | Ax_exp -> print_str_line ff "apply ax_exp." 
  | Seq rules ->
      assert false
  | Rot -> print_str_line ff "ex_rot." 

let (++) rule1 rule2 = match (rule1, rule2) with
  | Seq l1, Seq l2 -> Seq (l1 @ l2)
  | _ -> assert false

let is_rewriting = function
  | Rewrite _ | Rewrite_tens _ | Rewrite_one _  
  | Rewrite_wk_list _ | Rewrite_co_std_list _ | Rewrite_ax _ -> true
  | _ -> false  

let rec delete_rewritings = function
  | [] -> []
  | [x] -> [x] 
  | hd :: hd' :: tl' when is_rewriting hd && is_rewriting hd' ->
      delete_rewritings (hd' :: tl')
  | hd :: tl -> hd :: delete_rewritings tl 

let rec simplify = function 
  | Seq l -> Seq (delete_rewritings (List.map simplify l))
  | x -> x 

let rec proof_to_yalla_rule = function
  | Null -> Seq []
  | Node (sequent, rule, proof_list) ->
      let theta, gamma, l = 
        get_theta sequent, get_gamma sequent, get_list sequent in
      match rule with
        | Top_intro -> Seq [Top_r] ++ (proof_to_yalla_rule (List.hd proof_list))
        | Bottom_intro -> 
            Seq [Bot_r] ++ (proof_to_yalla_rule (List.hd proof_list))
        | One_intro -> 
            Seq [Rewrite_one (MapWn (Set_formula.elements theta)); Wk_list_r; One_r] ++
            (proof_to_yalla_rule (List.hd proof_list))
        | Par_intro ->
            let Par (f, g) :: l' = l in
            let theta_list = Set_formula.elements theta in
            Seq [Parr_r; Rewrite ((g :: f :: l') @ gamma, MapWn theta_list)] ++ 
            (proof_to_yalla_rule (List.hd proof_list))
        | Tensor_intro (l1, l2) ->
            let [br1; br2] = proof_list in
            let theta_list = Set_formula.elements theta in
            Seq [Rewrite_co_std_list (MapWn theta_list, gamma @ l); 
                 Co_std_list_r;        
                 Rewrite_tens 
                   (List.hd l, (l2, MapWn theta_list), (l1, MapWn theta_list));
                 Tens_r;
                 proof_to_yalla_rule br1; 
                 proof_to_yalla_rule br2]
        | With_intro ->
            let [br1; br2] = proof_list in
            Seq [With_r;
                 proof_to_yalla_rule br1; 
                 proof_to_yalla_rule br2]
        | Plus_intro_1 ->
            Seq [Plus_r1] ++ (proof_to_yalla_rule (List.hd proof_list)) 
        | Plus_intro_2 ->
            Seq [Plus_r2] ++ (proof_to_yalla_rule (List.hd proof_list))
        | OfCourse_intro ->
            let f = List.hd l in
            
            Seq [Rewrite ([f], MapWn (Set_formula.elements theta));
                 Oc_r] ++ (proof_to_yalla_rule (List.hd proof_list))
        | Whynot_intro ->
            let (Whynot f) :: l' = l in
            let theta_list = Set_formula.elements theta in
            if Set_formula.mem f theta then
              Seq [Rewrite (l @ gamma, MapWn theta_list); Wk_r; 
                   Rewrite (l' @ gamma, MapWn theta_list)] ++ 
              (proof_to_yalla_rule (List.hd proof_list))
            else
              Seq [Rewrite (l' @ gamma, MapWn (f :: theta_list))] ++
              (proof_to_yalla_rule (List.hd proof_list))
        | I1 ->
            let [f_dual], [f] = gamma, l in
            let theta_list = Set_formula.elements theta in
            if theta_list = [] then 
              Seq [Rewrite_ax (f, f_dual); Ax_exp]
            else
              Seq [Rewrite_wk_list (MapWn theta_list, [f; f_dual]);
                   Wk_list_r; Ax_exp]               
        | I2 -> 
            let [(Pos x)] = l in
            let theta'_list = 
              Set_formula.elements (Set_formula.remove (Neg x) theta) in
            Seq [Rewrite_wk_list (MapWn theta'_list, [Whynot (Neg x); Pos x]);
                 Wk_list_r; 
                 De_r;
                 Rot;
                 Ax_exp]
        | D1 (f, gamma') ->
            Seq [Rewrite (f :: gamma' @ l, MapWn (Set_formula.elements theta))] ++ 
            (proof_to_yalla_rule (List.hd proof_list))
 
        | D2 f -> 
            let theta'_list = Set_formula.elements (Set_formula.remove f theta)
            in
            Seq [Rewrite_co_std_list (MapWn [f], gamma @ map_wn theta'_list);
                 Co_std_list_r;
                 Rewrite (Whynot f :: gamma, MapWn (f :: theta'_list));
                 De_r] ++
            (proof_to_yalla_rule (List.hd proof_list))

        | R_async ->
            let f :: l' = l in
            Seq [Rewrite (l' @ (f :: gamma), MapWn (Set_formula.elements
            theta))] ++
            (proof_to_yalla_rule (List.hd proof_list))

        | R_sync -> Seq [] ++ (proof_to_yalla_rule (List.hd proof_list))

let block_counter = ref 0

let sign i = 
  if i mod 2 = 0 then
    String.make (i / 2) '+' ^ " "
  else
    String.make ((i + 1) / 2) '-' ^ " "

let cases = 
  [(1, "- "); (2, "+ "); (3, "-- "); (4, "++ "); (5, "--- "); (6, "+++ ")]

let indent i =
  if i mod 2 = 0 then
    let k = i / 2 in k * (k + 3)
  else
    let k = (i + 1) / 2 in k * (k + 3) - (k + 1)

let rec print_rules ff rules = 
  let rec print_rule ff = function
    | Seq l ->
        if !block_counter = 0 then begin 
          incr block_counter; 
          List.iter (print_rule ff) l;
          decr block_counter end
        else begin 
          print_str ff (sign (!block_counter)); 
          incr block_counter;
          if l = [] then decr block_counter 
          else
            let hd :: tl = l in
            print_rule ff hd;
            List.iter 
            (fun x -> 
              print_str ff (String.make (indent (!block_counter - 1)) ' ');
              print_rule ff x) tl;
              decr block_counter end
    | rule ->
        print_yalla_rule ff rule
  in 
  print_rule ff rules;
  print_str_line ff "Qed."

let rec string_of_vars = function
  | [] -> ""
  | [x] -> x
  | hd :: tl -> hd ^ " " ^ string_of_vars tl 

let string_of_goal l = 
  let s = 
    List.fold_left 
      (fun s f -> Set_var.union s (free_variables f)) Set_var.empty l in
  if Set_var.is_empty s then
    "Goal ll_ll "^ string_of_flist l ^ ".", ""
  else
    let vars = string_of_vars (Set_var.elements s) in
    "Goal forall " ^ vars ^ ", ll_ll " ^
    string_of_flist l ^ ".", "intros " ^ vars ^ "." 

(* Coq rules for the system ILLF *)

type mapoc = MapOc of formula list 

let map_oc = List.map (fun x -> OfCourse x) 

let print_moc ff (MapOc l) = 
  fprintf ff "map ioc %a" print_ill_yalla_flist l

type ill_yalla_rule = 
  | Ax_exp_ill
  | One_irr
  | One_ilr
  | Tens_irr
  | Tens_ilr
  | Top_irr
  | Zero_ilr
  | With_irr 
  | With_ilr1
  | With_ilr2
  | Plus_ilr
  | Plus_irr1
  | Plus_irr2
  | Lmap_irr
  | Lmap_ilr
  | Oc_irr
  | De_ilr
  | Wk_ilr
  | Wk_list_ilr
  | Co_ilr
  | Co_list_ilr  
  | Co_std_list_ilr
  | Rewrite_co_std_list_ilr of mapoc * formula list * formula
  | Rewrite_tens_irr of (mapoc * formula list) * (mapoc * formula list) * formula 
  | Rewrite_lmap_ilr of 
      mapoc * (mapoc * formula list) * formula list * formula
  
  | Rewrite_oc_irr of mapoc * formula
  | Rewrite_wk_list_ilr of formula list * mapoc * formula list * formula 
  | IRewrite of mapoc * formula list * formula
  | ISeq of ill_yalla_rule list

let ill_is_rewriting = function
  | Rewrite_co_std_list_ilr _ | Rewrite_tens_irr _ | Rewrite_lmap_ilr _ 
  | Rewrite_oc_irr _ | Rewrite_wk_list_ilr _ | IRewrite _ -> true
  | _ -> false 
      
let rec ill_delete_rewritings = function
  | [] -> []
  | [x] -> [x] 
  | hd :: hd' :: tl' when ill_is_rewriting hd && ill_is_rewriting hd' ->
      ill_delete_rewritings (hd' :: tl')
  | hd :: tl -> hd :: ill_delete_rewritings tl 

let rec ill_simplify = function 
  | ISeq l -> ISeq (ill_delete_rewritings (List.map ill_simplify l))
  | x -> x 

let (+++) rule1 rule2 = match (rule1, rule2) with
  | ISeq l1, ISeq l2 -> ISeq (l1 @ l2)
  | _ -> assert false 

let print_ill_yalla_rule ff = function
  | Ax_exp_ill -> print_str_line ff "apply ax_exp_ill." 
  | One_irr -> print_str_line ff "apply one_irr."
  | One_ilr -> print_str_line ff "apply one_ilr."
  | Tens_irr -> print_str_line ff "apply tens_irr." 
  | Tens_ilr -> print_str_line ff "apply tens_ilr."
  | Top_irr -> print_str_line ff "apply top_irr."
  | Zero_ilr -> print_str_line ff "apply zero_ilr."
  | With_irr -> print_str_line ff "apply with_irr." 
  | With_ilr1 -> print_str_line ff "apply with_ilr1."
  | With_ilr2 -> print_str_line ff "apply with_ilr2."
  | Plus_ilr -> print_str_line ff "apply plus_ilr."
  | Plus_irr1 -> print_str_line ff "apply plus_irr1."
  | Plus_irr2 -> print_str_line ff "apply plus_irr2."
  | Lmap_irr -> print_str_line ff "apply lmap_irr."
  | Lmap_ilr -> print_str_line ff "apply lmap_ilr."   
  | Oc_irr -> print_str_line ff "apply oc_irr."
  | De_ilr -> print_str_line ff "apply de_ilr."
  | Wk_ilr -> print_str_line ff "apply wk_ilr."
  | Wk_list_ilr -> print_str_line ff "apply wk_list_ilr." 
  | Co_ilr -> print_str_line ff "apply co_ilr." 
  | Co_list_ilr -> print_str_line ff "apply co_list_ilr."
  | Co_std_list_ilr -> print_str_line ff "apply co_std_list_ilr."
  | Rewrite_co_std_list_ilr (moc, l, f) ->
      fprintf ff "ex_solve (%a ++ %a) %a.\n@?"
      print_moc moc 
      print_ill_yalla_flist l
      print_ill_yalla_formula f
  | Rewrite_tens_irr ((moc1, l1), (moc2, l2), f) ->
      fprintf ff "ex_solve (%a ++ %a) ++ (%a ++ %a) %a.\n@?"
      print_moc moc1
      print_ill_yalla_flist l1
      print_moc moc2
      print_ill_yalla_flist l2
      print_ill_yalla_formula f
  | Rewrite_lmap_ilr (moc1, (moc2, l2), l1, f) ->
      fprintf ff "ex_solve (%a ++ (%a ++ %a) ++ %a) %a.\n@?"
      print_moc moc2 
      print_moc moc1 
      print_ill_yalla_flist l1
      print_ill_yalla_flist l2
      print_ill_yalla_formula f 
  | Rewrite_oc_irr (moc, f) ->
      fprintf ff "ex_solve (%a) %a.\n@?" 
      print_moc moc 
      print_ill_yalla_formula f
  | Rewrite_wk_list_ilr (l1, moc, l2, f) ->
      fprintf ff "ex_solve (%a ++ %a ++ %a) %a.\n@?"
      print_ill_yalla_flist l1
      print_moc moc 
      print_ill_yalla_flist l2
      print_ill_yalla_formula f
  | IRewrite (moc, l, f) ->
      fprintf ff "ex_solve (%a ++ %a) %a.\n@?"
      print_moc moc 
      print_ill_yalla_flist l
      print_ill_yalla_formula f
  | ISeq _ -> assert false

let rec ill_proof_to_yalla_rule = function
  | INull -> ISeq []
  | INode (sequent, rule, proof_list) -> 
      let theta, gamma, formula = 
        ill_get_theta sequent, ill_get_gamma sequent, ill_get_formula sequent in
      match rule with
        | Tensor_L -> 
            ISeq [Tens_ilr] +++
            (ill_proof_to_yalla_rule (List.hd proof_list))
        | Tensor_R (gamma1, gamma2) ->
            let theta_list = Set_formula.elements theta in
            let [br1; br2] = proof_list in
            let oc_theta = MapOc theta_list in 
            ISeq [Rewrite_co_std_list_ilr (oc_theta, gamma, formula);
                  Co_std_list_ilr;
                  Rewrite_tens_irr 
                    ((oc_theta, gamma1), (oc_theta, gamma2), formula);
                  Tens_irr;
                  ill_proof_to_yalla_rule br1;
                  ill_proof_to_yalla_rule br2] 
        | Impl_L (gamma1, gamma2) -> 
            let theta_list = Set_formula.elements theta in
            let lmap = List.hd gamma in
            let [br1; br2] = proof_list in
            let oc_theta = MapOc theta_list in
            ISeq [Rewrite_co_std_list_ilr 
                    (oc_theta, gamma, formula);
                  Co_std_list_ilr;
                  Rewrite_lmap_ilr 
                    (oc_theta, (oc_theta, lmap :: gamma2), gamma1, formula); 
                  Lmap_ilr;
                  ill_proof_to_yalla_rule br1;
                  ill_proof_to_yalla_rule br2]         
        | Impl_R ->
            let Impl (g, h) = formula in
            let theta_list = Set_formula.elements theta in
            let oc_theta = MapOc theta_list in
            ISeq [Lmap_irr; 
                  IRewrite (oc_theta, g :: gamma, h)] +++
            (ill_proof_to_yalla_rule (List.hd proof_list))
        | One_L -> 
            ISeq [One_ilr] +++
            (ill_proof_to_yalla_rule (List.hd proof_list))
        | One_R -> 
            let theta_list = Set_formula.elements theta in
            ISeq [Rewrite_wk_list_ilr ([], MapOc theta_list, gamma, formula);
                  Wk_list_ilr;
                  One_irr]
        | Init ->
            let theta_list = Set_formula.elements theta in
            ISeq [Rewrite_wk_list_ilr ([], MapOc theta_list, gamma, formula);
                  Wk_list_ilr;
                  Ax_exp_ill]      
        | Top_R -> ISeq [Top_irr]   
        | Zero_L -> 
            ISeq [Zero_ilr]
        | OfCourse_L -> 
            let OfCourse f = List.hd gamma in
            let theta_list = Set_formula.elements theta in
            if Set_formula.mem f theta then
              ISeq [
                IRewrite (MapOc theta_list, gamma, formula);
                Wk_ilr] +++
              (ill_proof_to_yalla_rule (List.hd proof_list))
            else
              ISeq [IRewrite 
                      ((MapOc (f :: theta_list)), List.tl gamma, formula)] +++
              (ill_proof_to_yalla_rule (List.hd proof_list))
        | OfCourse_R ->
            let theta_list = Set_formula.elements theta in
            let OfCourse f = formula in
            ISeq [Rewrite_oc_irr (MapOc theta_list, formula);
                  Oc_irr;
                  IRewrite (MapOc theta_list, [], f)] +++
            (ill_proof_to_yalla_rule (List.hd proof_list)) 
        | With_R ->
            let [br1; br2] = proof_list in 
            ISeq [With_irr;
                  ill_proof_to_yalla_rule br1;
                  ill_proof_to_yalla_rule br2]                            
        | With_L_1 -> 
            ISeq [With_ilr1] +++
            (ill_proof_to_yalla_rule (List.hd proof_list))
            
        | With_L_2 ->
            ISeq [With_ilr2] +++
            (ill_proof_to_yalla_rule (List.hd proof_list))
            
        | Plus_L -> 
            let [br1; br2] = proof_list in
            ISeq [Plus_ilr;
                  ill_proof_to_yalla_rule br1;
                  ill_proof_to_yalla_rule br2]
        | Plus_R_1 ->  
            ISeq [Plus_irr2] +++
            (ill_proof_to_yalla_rule (List.hd proof_list))
        | Plus_R_2 ->
            ISeq [Plus_irr1] +++
            (ill_proof_to_yalla_rule (List.hd proof_list))
        | Copy f -> 
            let theta' = Set_formula.remove f theta in
            let theta'_list = Set_formula.elements theta' in
            let theta_list = Set_formula.elements theta in
            ISeq [Rewrite_co_std_list_ilr 
                    (MapOc [f], map_oc theta'_list @ gamma, formula);
                  Co_std_list_ilr;
                  IRewrite ((MapOc theta_list), OfCourse f :: gamma, formula);
                  De_ilr] +++
            (ill_proof_to_yalla_rule (List.hd proof_list)) 
        | _ ->
            ill_proof_to_yalla_rule (List.hd proof_list)
        
let rec print_ill_rules ff rules = 
  let rec print_rule ff = function
    | ISeq l ->
        if !block_counter = 0 then begin 
          incr block_counter; 
          List.iter (print_rule ff) l;
          decr block_counter end
        else begin 
          print_str ff (sign (!block_counter)); 
          incr block_counter;
          if l = [] then decr block_counter 
          else
            let hd :: tl = l in
            print_rule ff hd;
            List.iter 
            (fun x -> 
              print_str ff (String.make (indent (!block_counter - 1)) ' ');
              print_rule ff x) tl;
              decr block_counter end
    | rule ->
        print_ill_yalla_rule ff rule
  in 
  print_rule ff rules;
  print_str_line ff "Qed."

let print_ill_goal ff = function
  | Active (_, _, gamma, formula) ->
      let s =
        List.fold_left 
          (fun s f -> 
             Set_var.union s (free_variables f)) (free_variables formula) gamma 
      in
      if Set_var.is_empty s then
        fprintf ff "Goal ill_ill %a %a.\nProof.\n@?"
        print_ill_yalla_flist gamma
        print_ill_yalla_formula formula
      else   
        let vars = string_of_vars (Set_var.elements s) in
        fprintf ff "Goal forall %s, ill_ill %a %a.\nProof.\nintros %s.\n@?"
        vars 
        print_ill_yalla_flist gamma
        print_ill_yalla_formula formula
        vars 
  | _ -> assert false  

let nb_levels s = 
  let n = ref 0 in
  for i = 0 to String.length s - 1 do
    (if s.[i] = '/' then incr n);
  done;
  !n + 1

let rec climb level = 
  if level = 0 then "."
  else 
    if level = 1 then "../"
    else climb (level - 1) ^ "../"

let output_proof_ll l proof filename = 
  let oc = open_out filename in
  let ff = formatter_of_out_channel oc in 
  let goal, intros = string_of_goal l in
  (*print_str_line ff 
  ("Add LoadPath \"" ^ climb (nb_levels filename) ^ "\".");*)
  print_str_line ff "Require Import miniyalla.";
  print_str_line ff goal;
  print_str_line ff "Proof.";
  (if intros <> "" then print_str_line ff intros);
  print_rules ff (simplify (proof_to_yalla_rule proof));
  close_out oc

let output_proof_ill sequent proof filename = 
  let dir, base = Filename.dirname filename, Filename.basename filename in
  let oc = open_out ("../miniyalla/ill_tests/" ^ dir ^ "/proof" ^ base ^ ".v") in
  let ff = formatter_of_out_channel oc in
  print_str_line ff 
  ("Add LoadPath \"" ^ climb (nb_levels filename) ^ "\".");
  print_str_line ff "Require Import ill.";
  print_ill_goal ff sequent;
  print_ill_rules ff (ill_simplify (ill_proof_to_yalla_rule proof));
  close_out oc
