(*** Forward proof search in ILL using the focused inverse method ***)

open Formula
open Fctns
open Fctns_inv
open Format
open Printer

(* [max_nb_copies] is maximum number of occurrences of a sequent in the list
   of sequents used for generating new provable sequents. *)
let max_nb_copies = ref 1

(** Manipulation of frontier propositions **)

type frontier = 
  Set_formula.t (* + *) * Set_formula.t (* - *) * Set_formula.t (* -!*)

let print_frontier ff (s, t, u) =
  fprintf ff "(%a | %a | %a)"
  print_formula_set s
  print_formula_set t
  print_formula_set u

let empty_frontier = (Set_formula.empty, Set_formula.empty, Set_formula.empty)

let union_frontier (s, t, u) (s', t', u') =
  (Set_formula.union s s', Set_formula.union t t', Set_formula.union u u')

let rec focal_neg formula = match [@warning "-8"] formula with
  | Pos _ -> empty_frontier
  | Tensor (f, g) -> active_neg formula
  | Plus (f, g) -> active_neg formula 
  | With (f, g) -> 
      union_frontier (focal_neg f) (focal_neg g)
  | Impl (f, g) -> 
      union_frontier (focal_pos f) (focal_neg g)
  | OfCourse f -> active_neg formula
  | One -> empty_frontier
  | Top -> empty_frontier
  | Zero -> empty_frontier

and active_neg formula = match [@warning "-8"] formula with
  | Pos _ ->
      (Set_formula.empty, Set_formula.singleton formula, Set_formula.empty)
  | Tensor (f, g) -> 
      union_frontier (active_neg f) (active_neg g)
  | Plus (f, g) ->
      union_frontier (active_neg f) (active_neg g)
  | With (f, g) ->
      let (s, t, u) = focal_neg formula in
      (s, Set_formula.add formula t, u)
  | Impl (f, g) -> 
      focal_neg formula
  | OfCourse f -> 
      let (s, t, u) = focal_neg f in
      (s, t, Set_formula.add f u)
  | One -> empty_frontier
  | Top -> empty_frontier
  | Zero -> empty_frontier

and focal_pos formula = match [@warning "-8"] formula with 
  | Pos _ -> 
      (Set_formula.singleton formula, Set_formula.empty, Set_formula.empty)
  | Tensor (f, g) -> 
      union_frontier (focal_pos f) (focal_pos g)
  | Plus (f, g) ->
      union_frontier (focal_pos f) (focal_pos g)
  | With (f, g) -> active_pos formula
  | Impl (f, g) -> active_pos formula
  | OfCourse f -> active_pos f
  | One -> empty_frontier
  | Top -> empty_frontier
  | Zero -> empty_frontier

and active_pos formula = match [@warning "-8"] formula with
  | Pos _ -> 
      (Set_formula.singleton formula, Set_formula.empty, Set_formula.empty)
  | Tensor (f, g) -> 
      let (s, t, u) = focal_pos formula in
      (Set_formula.add formula s, t, u) 
  | Plus (f, g) ->
      let (s, t, u) = focal_pos formula in
      (Set_formula.add formula s, t, u)
  | With (f, g) -> union_frontier (active_pos f) (active_pos g)
  | Impl (f, g) -> union_frontier (active_neg f) (active_pos g)
  | OfCourse f -> 
      let (s, t, u) = focal_pos f in
      (Set_formula.add formula s, t, u)      
  | One -> empty_frontier
  | Top -> empty_frontier  
  | Zero -> empty_frontier

(** Forward Sequents **)

type forward_sequent = Forw of Set_formula.t * context * formula option

let is_weak (Forw (_, ctxt, _)) = match ctxt with
  | Weight (w, _) -> w
  | _ -> false 

let is_strong x = not (is_weak x)

let [@warning "-8"] print_forward_sequent ff (Forw (theta, Weight (w, gamma), opt)) =
  if w then
    fprintf ff "Weak(%a | %a ==> %a)@?"
    print_formula_list (Set_formula.elements theta)
    print_formula_list (map_to_list gamma)
    print_option opt
  else begin
    fprintf ff "Strong(%a | %a ==> %a)@?"
    print_formula_list (Set_formula.elements theta)
    print_formula_list (map_to_list gamma)
    print_option opt end

let print_sequent_list ff l =
  fprintf ff "{ %a }@?" (pp_print_list ~pp_sep:print_sep print_forward_sequent)
  l

let get_formula gamma = 
  List.map fst (List.filter (fun (_, n) -> n > 0) (Map_formula.bindings gamma))

let calculate_frontier (theta, gamma, f) =
  let theta_list = Set_formula.elements theta in
  let gamma_list = map_to_list gamma in
  let pos = Set_formula.singleton f in
  let neg = Set_formula.of_list gamma_list in
  let neg_oc = Set_formula.of_list theta_list in 
  let l = focal_pos f :: (List.map focal_neg (theta_list @ gamma_list)) in
  List.fold_left union_frontier (pos, neg, neg_oc) l 

(* Sequent combinators *) 

let tens_seq (Forw (theta, ctxt, opt)) (Forw (theta', ctxt', opt')) = 
  match opt, opt' with
    | None, None -> begin try          
        [Forw (Set_formula.union theta theta', simp_ctxt (CTimes (ctxt, ctxt')),  
         None)] with ContextError -> [] end 
    | _ -> [] 

let ofcourse_seq (Forw (theta, ctxt, opt)) = match ctxt with
  | Weight (w, map) when is_empty map ->
      if opt = None then [Forw (theta, Weight (false, map), None)]
      else []
  | _ -> [] 
 
let impl_seq (Forw (theta, ctxt, opt)) (Forw (theta', ctxt', opt')) = 
  match opt, opt' with 
    | None, _ -> begin try
        [Forw (Set_formula.union theta theta', simp_ctxt (CTimes (ctxt, ctxt')),
         opt')] with ContextError -> [] end
    | _ -> [] 

let with_seq (Forw (theta, ctxt, opt)) (Forw (theta', ctxt', opt')) = 
  match opt, opt' with
    | None, None -> begin try 
        [Forw (Set_formula.union theta theta', simp_ctxt (CPlus (ctxt, ctxt')), 
         None)] with ContextError -> [] end 
    | _ -> []

let plus_seq (Forw (theta, ctxt, opt)) (Forw (theta', ctxt', opt')) = 
  match opt, opt' with
    | None, _ -> begin try
        [Forw (Set_formula.union theta theta', simp_ctxt (CPlus (ctxt, ctxt')), 
         opt')] with ContextError -> [] end
    | _, None -> begin try
        [Forw (Set_formula.union theta theta', simp_ctxt (CPlus (ctxt, ctxt')),
         opt)] with ContextError -> [] end 
    | _ -> [] 

let backslash opt1 opt2 = match opt2 with
  | None -> opt1
  | _ when opt1 = opt2 -> None
  | _ -> raise NoValue   

let rec r_focus f seqlist tbl = match f with
  | Tensor (g, h) ->
      let rec r_focus_aux acc k = match k with
        | -1 -> acc
        | _ -> 
            let seq1, seq2 = split_list seqlist k in 
            r_focus_aux 
              (map_flat_product tens_seq 
                (r_focus g seq1 tbl) (r_focus h seq2 tbl) @ acc) (k-1) in
      let k = fast_exp_2 (List.length seqlist) - 1 in r_focus_aux [] k
  | Plus (g, h) -> 
      r_focus g seqlist tbl @ r_focus h seqlist tbl
  | One -> 
      if seqlist = [] then 
        [Forw (Set_formula.empty, Weight (false, Map_formula.empty), None)]
      else [] 
  | OfCourse g ->  
      List.concat 
        (List.map ofcourse_seq 
           (act (Set_formula.empty, Map_formula.empty, [], Some g) seqlist tbl))
  | _ when right_async f ->
      let f' = try Hashtbl.find tbl f with Not_found -> f in 
      act (Set_formula.empty, Map_formula.empty, [], Some f') seqlist tbl
  
  | Pos _ -> act (Set_formula.empty, Map_formula.empty, [], Some f) seqlist tbl
  | _ -> []

and l_focus f seqlist tbl = match f with
  | With (g, h) -> l_focus g seqlist tbl @ l_focus h seqlist tbl
  | Impl (g, h) ->
      let rec l_focus_aux acc k = match k with
        | -1 -> acc
        | _ -> 
            let seq1, seq2 = split_list seqlist k in
            l_focus_aux 
              (map_flat_product impl_seq 
                 (r_focus g seq1 tbl) (l_focus h seq2 tbl) @ acc) (k-1) in
      let k = fast_exp_2 (List.length seqlist) - 1 in l_focus_aux [] k
  | Top -> [] 
  | Pos _ -> 
      if seqlist = [] then 
        [Forw 
           (Set_formula.empty, Weight (false, Map_formula.empty), Some f)]
      else 
        act (Set_formula.empty, Map_formula.empty, [f], None) seqlist tbl
  | _ when left_async f -> 
      act (Set_formula.empty, Map_formula.empty, [f], None) seqlist tbl
  | _ -> [] 

and act' (theta, gamma, l, opt) seqlist tbl = match opt with
  | Some (With (f, g)) -> 
      let rec act_aux acc k = match k with
        | -1 -> acc
        | _ ->
            let seq1, seq2 = split_list seqlist k in
            act_aux 
              (map_flat_product with_seq 
                 (act (theta, gamma, l, Some f) seq1 tbl) 
                 (act (theta, gamma, l, Some g) seq2 tbl) @ acc)
              (k - 1) in
      let k = fast_exp_2 (List.length seqlist) - 1 in act_aux [] k
  | Some Top ->
      if seqlist = [] then [Forw (theta, Weight (true, gamma), None)]
      else []
  | Some (Impl (f, g)) -> 
      act (theta, gamma, f :: l, Some g) seqlist tbl @
      List.filter is_weak (act (theta, gamma, l, Some g) seqlist tbl)
  | _ -> match l with
      | [] -> begin        
          try
            let [@warning "-8"] [Forw (theta', Weight (w, gamma'), Some f)] = 
              seqlist in
            if opt = None then
              if inclusion_set theta theta' then
                [Forw (Set_formula.diff theta' theta, Weight (w, diff gamma'
                 gamma), Some f)]
              else []
            else begin  
              let g = get_op opt in
              let g' = try Hashtbl.find tbl g with Not_found -> g in 
              if f = g' then
                if inclusion_set theta theta' then (
                  [Forw (Set_formula.diff theta' theta, Weight (w, diff gamma'
                   gamma), None)])
                else []
              else [] end
          with _ -> try 
            let [@warning "-8"] [Forw (theta', Weight (true, gamma'), None)] = seqlist in
            if inclusion_set theta theta' then
              [Forw (Set_formula.diff theta' theta, Weight (true, diff gamma'
               gamma), None)]
            else []
            with _ -> [] end
      | hd :: tl -> match [@warning "-8"] hd with
          | Tensor (f, g) ->
              act (theta, gamma, g :: f :: tl, opt) seqlist tbl @
              List.filter is_weak (act (theta, gamma, f :: tl, opt) seqlist tbl) 
              @
              List.filter is_weak (act (theta, gamma, g :: tl, opt) seqlist tbl)
          | Plus (f, g) ->
              let rec act_aux acc k = match k with
                | -1 -> acc
                | _ -> 
                    let seq1, seq2 = split_list seqlist k in
                    act_aux
                      (map_flat_product plus_seq 
                         (act (theta, gamma, f :: tl, opt) seq1 tbl)
                         (act (theta, gamma, g :: tl, opt) seq2 tbl) @ acc)
                      (k - 1) in
              let k = fast_exp_2 (List.length seqlist) - 1 in act_aux [] k
          | Zero -> []
          | One ->
              act (theta, gamma, tl, opt) seqlist tbl 
          | OfCourse f ->
              act (Set_formula.add f theta, gamma, tl, opt) seqlist tbl @
              List.filter is_strong (act (theta, gamma, tl, opt) seqlist tbl)
          | _ when left_sync hd -> 
              act (theta, insert hd gamma, tl, opt) seqlist tbl

and act (theta, gamma, l, opt) seqlist tbl = 
  if List.mem Zero l && seqlist = [] then
    [Forw (Set_formula.empty, Weight (true, Map_formula.empty), None)] 
  else act' (theta, gamma, l, opt) seqlist tbl

let derived_rule_pos seqlist f tbl =
  let new_sequent (Forw (theta, ctxt, opt)) = match opt with
    | None -> [Forw (theta, ctxt, Some f)]
    | _ -> [] in
  List.concat (List.map new_sequent (r_focus f seqlist tbl))
  
let derived_rule_neg_theta theta_0 seqlist f tbl =
  let bl = Set_formula.mem f theta_0 in
  let new_sequent (Forw (theta, ctxt, opt)) = 
    [Forw ((if bl then theta else Set_formula.add f theta), ctxt, opt)] in 
  List.concat (List.map new_sequent (l_focus f seqlist tbl))

let derived_rule_neg_gamma gamma_0 seqlist f tbl =
  let [@warning "-8"] new_sequent (Forw (theta, Weight (w, ctxt), opt)) = 
    if (try Map_formula.find f gamma_0 with Not_found -> 0) = 0 || 
      (try Map_formula.find f gamma_0 with Not_found -> 0) >=
      (try Map_formula.find f ctxt + 1 with Not_found -> 1)
    then 
      [Forw (theta, Weight (w, insert f ctxt), opt)] 
    else [] in
  List.concat (List.map new_sequent (l_focus f seqlist tbl))

let proved = ref false

let eq_seq (Forw (theta, ctxt, opt)) (Forw (theta', ctxt', opt')) =
  let [@warning "-8"] Weight (w, gamma) = ctxt in
  let [@warning "-8"] Weight (w', gamma') = ctxt' in
  eq_set theta theta' && w = w' && eq_map gamma gamma' && opt = opt'

module Set_sequent = 
  Set.Make(struct 
    type t = forward_sequent 
    let compare x y = 
      if eq_seq x y then 0 else Pervasives.compare x y end) 

let print_sequent_set ff s =
  print_sequent_list ff (Set_sequent.elements s)

let database = ref Set_sequent.empty

let check_new_sequent (theta, gamma, f) (Forw (theta', ctxt', opt')) = 
  match ctxt' with
    | Weight (w, gamma') ->
        if not w then begin 
          inclusion_set theta' theta && eq_map gamma gamma' && opt' = Some f end
        else 
          inclusion_set theta' theta && inclusion gamma' gamma && 
          (opt' = None || opt' = Some f)
    | _ -> assert false

let subsumption sequent1 sequent2 = match (sequent1, sequent2) with
  | Forw (theta, Weight (w, gamma), opt), 
    Forw (theta', Weight (w', gamma'), opt') ->
      if not w && not w' then begin  
        inclusion_set theta theta' && eq_map gamma gamma' && is_some opt && 
        opt = opt' end
      else 
        if w = true then 
          inclusion_set theta theta' && inclusion gamma gamma' && 
          inclusion_op opt opt'
        else false
  | _ -> false 

let insert_data x goal tbl =
  (if check_new_sequent goal x then proved := true);
  let subsumed = ref false in
  let check_subsumption new_sequent sequent =
    (if subsumption new_sequent sequent && not (eq_seq new_sequent sequent) then 
      database := Set_sequent.remove sequent !database);
    if subsumption sequent new_sequent then
      subsumed := true 
  in
  let Forw (theta, ctxt, opt) = x in
  let x' = match opt with 
    | None -> x
    | Some f -> 
        Forw (theta, ctxt, try Some (Hashtbl.find tbl f) with Not_found -> opt)
  in 
  Set_sequent.iter (check_subsumption x') !database; 
  if not !subsumed then begin
    database := Set_sequent.add x' !database;
    false
    end
  else 
    true

let sub_formulas_seq (theta, gamma, f) =
  sub_formulas_l (f :: map_to_list gamma @ Set_formula.elements theta)
  
let find_theta_sub sequent =
  let theta, gamma, f = sequent in
  let props = f :: Set_formula.elements theta @ (map_to_list gamma) in
  let sub = sub_formulas_seq sequent in
  let check_theta_all x =
    Set_formula.mem x sub && 
    List.fold_left (fun res f -> res && check_theta x f) true props in
  let tbl = Hashtbl.create (Set_formula.cardinal sub) in
  let rec check_theta_map_iter x = 
    try Hashtbl.find tbl x  
    with Not_found ->
      if not (check_theta_all x) then x
      else begin
        let y = check_theta_map_iter (OfCourse x) in
        Hashtbl.add tbl x y;
        y end in 
  Set_formula.iter (fun x -> Hashtbl.add tbl x (check_theta_map_iter x)) sub;
  tbl

let prove sequent =
  let (theta, gamma, f) = sequent in
  let sub_pos, sub_gamma, sub_theta = calculate_frontier sequent in 
  let tbl = find_theta_sub sequent in   
  let rec apply_rules () =
    if !proved then ()
    else begin 
      let seqlist = Set_sequent.elements !database in
      let saturated = ref true in
      let len = List.length seqlist in
      let rec apply_sublist m k a b =  
        if m = !max_nb_copies + 1 then ()
        else begin 
          if k = len + 1 then apply_sublist (m + 1) 0 0 (fast_exp (m + 2) (len - 1) - 1)
          else begin
            let seqlist' = 
              if m = 0 || k = len || seqlist = [] then [] 
              else generate_sublist k m seqlist a b in
            Set_formula.iter
              (fun f ->
                 if !proved then ()
                 else
                   let l = derived_rule_pos seqlist' f tbl in
                   List.iter 
                     (fun x -> 
                        saturated := insert_data x sequent tbl && !saturated) l) 
                     sub_pos;
            Set_formula.iter   
              (fun f ->
                 if !proved then ()
                 else
                   let l = derived_rule_neg_gamma gamma seqlist' f tbl in
                   List.iter 
                     (fun x -> 
                        saturated := insert_data x sequent tbl && !saturated) l) 
                     sub_gamma;
            Set_formula.iter 
              (fun f ->
                 if !proved then ()
                 else 
                   let l = derived_rule_neg_theta theta seqlist' f tbl in
                   List.iter 
                     (fun x -> 
                        saturated := insert_data x sequent tbl && !saturated) l) 
                     sub_theta;
            if m = 0 then 
              apply_sublist 1 0 0 (fast_exp 2 (len - 1) - 1)
            else  
              if a = 0 then 
                if b = 0 then 
                  apply_sublist 
                    m (k + 1) (fast_exp m (k + 1) - 1) 
                    (fast_exp (m + 1) (len - k - 2) - 1)
                else
                  apply_sublist m k (fast_exp m (len - k) - 1) (b - 1)
              else
                apply_sublist m k (a - 1) b end end in
      apply_sublist 0 0 0 0;
      if !saturated then ()
      else apply_rules () end in
  apply_rules ()

let rec prove_general = function
  | Active (theta, gamma, l, f) -> begin match [@warning "-8"] f with
      | With (g, h) ->
          prove_general (Active (theta, gamma, l, g)); 
          if !proved then 
            prove_general (Active (theta, gamma, l, h))
          else ()
      | Top -> proved := true
      | Impl (g, h) ->
          prove_general (Active (theta, gamma, g :: l, h))
      | _ when right_sync f -> begin match l with
          | [] -> 
              let omega = 
                List.fold_left
                  (fun res f ->
                     Map_formula.add f 
                      (try Map_formula.find f res + 1 with Not_found -> 1) res)
                  Map_formula.empty gamma in
              prove (theta, omega, f)
          | hd :: tl -> begin match [@warning "-8"] hd with 
              | Tensor (g, h) -> 
                  prove_general (Active (theta, gamma, h :: g :: tl, f))
              | Plus (g, h) ->
                  prove_general (Active (theta, gamma, g :: tl, f));
                  if !proved then begin 
                    proved := false;
                    database := Set_sequent.empty;
                    prove_general (Active (theta, gamma, h :: tl, f)) end
              | OfCourse g ->
                  prove_general (Active (Set_formula.add g theta, gamma, tl, f))
              | Zero -> proved := true
              | One -> 
                  prove_general (Active (theta, gamma, tl, f))
              | _ when left_sync hd -> 
                  prove_general (Active (theta, hd :: gamma, tl, f)) end end end
  | _ -> assert false 

let prove_file file =
  let t = Sys.time () in
  let f = open_in file in
  let buf = Lexing.from_channel f in
  let (formula_list1, formula_list2) = Parser.file Lexer.token buf in
  let omega = formula_list1 in 
  let [@warning "-8"] [formula] = formula_list2 in
  let bwd_sequent = Active (Set_formula.empty, [], omega, formula) in
  proved := false;
  prove_general bwd_sequent;
  let exec_time = Sys.time () -. t in
  (!proved, exec_time)

let prove_sequent sequent bound =
  proved := false;
  max_nb_copies := bound;
  let t = Sys.time () in
  prove_general sequent;
  (!proved, Sys.time () -. t)
