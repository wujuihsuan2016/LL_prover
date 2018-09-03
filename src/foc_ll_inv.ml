open Formula
open Fctns 
open Format
open Fctns_inv
open Printer

let max_nb_copies = ref 1

type ll_forward_sequent = Fwd of Set_formula.t * context

let is_weak (Fwd (_, ctxt)) = match ctxt with
  | Weight (w, _) -> w
  | _ -> false

let is_strong x = not (is_weak x)

let [@warning "-8"] print_forward_sequent ff 
    (Fwd (theta, Weight (w, gamma))) =
  if w then
    fprintf ff "Weak (%a | %a)@?"
    print_formula_list (Set_formula.elements theta)
    print_formula_list (map_to_list gamma)
  else
    fprintf ff "Strong(%a | %a)@?"
    print_formula_list (Set_formula.elements theta) 
    print_formula_list (map_to_list gamma)

let print_sequent_list ff l =
  fprintf ff "{ %a }@?" 
  (pp_print_list ~pp_sep:print_sep print_forward_sequent) l

let tens_seq (Fwd (theta, ctxt)) (Fwd (theta', ctxt')) =
  try [Fwd (Set_formula.union theta theta', simp_ctxt (CTimes (ctxt, ctxt')))]
  with ContextError -> []

let with_seq (Fwd (theta, ctxt)) (Fwd (theta', ctxt')) = 
  try [Fwd (Set_formula.union theta theta', simp_ctxt (CPlus (ctxt, ctxt')))] 
  with ContextError -> []   

let ofcourse_seq (Fwd (theta, ctxt)) = match ctxt with
  | Weight (_, gamma) ->
      [Fwd (theta, Weight (false, gamma))]
  | _ -> []

let rec focus f seqlist tbl = match f with
  | Tensor (g, h) ->
      let rec focus_aux acc k = match k with
        | -1 -> acc 
        | _ ->
            let seq1, seq2 = split_list seqlist k in
            focus_aux 
              (map_flat_product tens_seq
                (focus g seq1 tbl) (focus h seq2 tbl) @ acc) (k - 1) in
      let k = fast_exp_2 (List.length seqlist) - 1 in focus_aux [] k
  | Plus (g, h) ->
      focus g seqlist tbl @ focus h seqlist tbl 
  | One ->
      if seqlist = [] then
        [Fwd (Set_formula.empty, Weight (false, Map_formula.empty))]
      else []
  | OfCourse g ->
      List.concat
        (List.map ofcourse_seq 
           (act (Set_formula.empty, Map_formula.empty, [g]) seqlist tbl))
  | Neg x -> 
      if seqlist = [] then
        let f' = try Hashtbl.find tbl (Pos x) with Not_found ->
          (Pos x) in 
        let map = Map_formula.add f' 1 Map_formula.empty in
        [Fwd (Set_formula.empty, Weight (false, map))]
      else
        let f' = try Hashtbl.find tbl f with Not_found -> f in 
        act (Set_formula.empty, Map_formula.empty, [f']) seqlist tbl
  | _ ->
      let f' = try Hashtbl.find tbl f with Not_found -> f in 
      act (Set_formula.empty, Map_formula.empty, [f']) seqlist tbl

and act (theta, gamma, l) seqlist tbl = match l with
  | [] -> begin
      try 
        let [@warning "-8"] [Fwd (theta', Weight (w, gamma'))] = seqlist in
        let gamma'' = 
          map_map (Hashtbl.find tbl) gamma in
        [Fwd (Set_formula.diff theta' theta, Weight (w, diff gamma' gamma''))]
      with _ -> [] end
  | hd :: tl -> match hd with
      | With (f, g) ->
          let rec act_aux acc k = match k with
            | -1 -> acc
            | _ -> 
                let seq1, seq2 = split_list seqlist k in
                act_aux 
                  (map_flat_product with_seq 
                     (act (theta, gamma, f :: tl) seq1 tbl)
                     (act (theta, gamma, g :: tl) seq2 tbl) @ acc) (k - 1) in
          let k = fast_exp_2 (List.length seqlist) - 1 in act_aux [] k
      | Par (f, g) ->
          act (theta, gamma, g :: f :: tl) seqlist tbl @
          List.filter is_weak (act (theta, gamma, g :: tl) seqlist tbl) @
          List.filter is_weak (act (theta, gamma, f :: tl) seqlist tbl)
      | Top -> 
          [Fwd (Set_formula.empty, Weight (true, Map_formula.empty))]
      | Bottom ->
          act (theta, gamma, tl) seqlist tbl
      | Whynot f ->
          act (Set_formula.add f theta, gamma, tl) seqlist tbl @
          List.filter is_strong (act (theta, gamma, tl) seqlist tbl)
      | _ -> 
          act (theta, insert hd gamma, tl) seqlist tbl

let derived_rule_pos gamma_0 seqlist f tbl =
  let f' = try Hashtbl.find tbl f with Not_found -> f in  
  let [@warning "-8"] new_sequent (Fwd (theta, Weight (w, ctxt))) = 
    if not (Map_formula.mem f' gamma_0) || 
       (try Map_formula.find f' gamma_0 with Not_found -> 0) >= 
       (try Map_formula.find f' ctxt + 1 with Not_found -> 1)
    then
      [Fwd (theta, Weight (w, insert f' ctxt))]
    else [] in
  List.concat (List.map new_sequent (focus f seqlist tbl))

let derived_rule_theta theta_0 seqlist f tbl = 
  let bl = Set_formula.mem f theta_0 in
  let new_sequent (Fwd (theta, ctxt)) = 
    Fwd ((if bl then theta else Set_formula.add f theta), ctxt) in
  List.map new_sequent (focus f seqlist tbl)

let proved = ref false

let eq_seq (Fwd (theta, ctxt)) (Fwd (theta', ctxt')) =
  let [@warning "-8"] Weight (w, gamma) = ctxt in
  let [@warning "-8"] Weight (w', gamma') = ctxt' in
  eq_set theta theta' && w = w' && eq_map gamma gamma' 

module Set_sequent = 
  Set.Make (struct
    type t = ll_forward_sequent 
    let compare x y =
      if eq_seq x y then 0 else Pervasives.compare x y end)

let print_sequent_set ff s =
  print_sequent_list ff (Set_sequent.elements s)

let check_new_sequent (theta, gamma) (Fwd (theta', ctxt')) = match ctxt' with
  | Weight (w, gamma') ->
      if not w then 
        inclusion_set theta' theta && eq_map gamma' gamma
      else
        inclusion_set theta' theta && inclusion gamma' gamma 
  | _ -> assert false

let subsumption sequent1 sequent2 = match (sequent1, sequent2) with
  | Fwd (theta, Weight (w, gamma)), Fwd (theta', Weight (w', gamma')) ->
      if not w && not w' then 
        inclusion_set theta theta' && eq_map gamma gamma'
      else
        if w = true then
          inclusion_set theta theta' && inclusion gamma gamma'
        else false
  | _ -> false

let database = ref Set_sequent.empty

let insert_data x goal = 
  (if check_new_sequent goal x then proved := true);
  let subsumed = ref false in
  let check_subsumption new_sequent sequent =
    (if subsumption new_sequent sequent && not (eq_seq new_sequent sequent) then
       database := Set_sequent.remove sequent !database);
    if subsumption sequent new_sequent then subsumed := true
  in
  Set_sequent.iter (check_subsumption x) !database;
  if not !subsumed then begin
    database := Set_sequent.add x !database;
    false end
  else
    true

type frontier = Set_formula.t * Set_formula.t

let empty_frontier = (Set_formula.empty, Set_formula.empty)

let union_frontier (s, t) (s', t') = (Set_formula.union s s', Set_formula.union
t t')

let rec focal formula = match formula with
  | Pos _ -> (Set_formula.singleton formula, Set_formula.empty) 
  | Neg _ -> empty_frontier 
  | OfCourse f -> active f
  | Whynot f ->
      active formula
  | Tensor (f, g) | Plus (f, g) -> 
      union_frontier (focal f) (focal g) 
  | With _ | Par _ -> active formula 
  | One | Top | Bottom | Zero -> empty_frontier 
  | Impl _ -> assert false

and active formula = match formula with
  | Pos _ | Neg _ -> (Set_formula.singleton formula, Set_formula.empty)
  | Tensor (f, g) | Plus (f, g) ->
      let (s, t) = focal formula in
      (Set_formula.add formula s, t)
  | With (f, g) | Par (f, g) -> union_frontier (active f) (active g)
  | Whynot f -> 
      let (s, t) = focal f in
      (s, Set_formula.add f t)
  | OfCourse f -> 
      let (s, t) = focal f in (Set_formula.add formula s, t)
  | One | Top | Bottom | Zero -> empty_frontier
  | Impl _ -> assert false
  
let calculate_frontier (theta, gamma) = 
  let theta_list = Set_formula.elements theta in
  let gamma_list = map_to_list gamma in
  let pos = Set_formula.of_list gamma_list in
  let pos_wn = Set_formula.of_list theta_list in
  let l = List.map focal (theta_list @ gamma_list) in
  List.fold_left union_frontier (pos, pos_wn) l

let find_theta_sub sequent = 
  let theta, gamma = sequent in
  let props = Set_formula.elements theta @ map_to_list gamma in
  let sub = sub_formulas_l props in
  let check_theta_all x = 
    Set_formula.mem x sub && 
    List.fold_left 
      (fun res f -> res && check_theta_ll x (neg_formula x) f) true props in
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
  let (theta, gamma) = sequent in
  let sub_pos, sub_theta = calculate_frontier sequent in
  let tbl = if true then find_theta_sub sequent else Hashtbl.create 30 in
  let rec apply_rules () =
    if !proved then () 
    else begin 
      let seqlist = Set_sequent.elements !database in
      let saturated = ref true in
      let len = List.length seqlist in
      let rec apply_sublist m k a b = 
        if m = !max_nb_copies + 1 then ()
        else begin
          if k = len + 1 then 
            apply_sublist (m + 1) 0 0 (fast_exp (m + 2) (len - 1) - 1)
          else
            begin
              let seqlist' = 
                if m = 0 || k = len || seqlist = [] then [] 
                else generate_sublist k m seqlist a b in
              Set_formula.iter 
                (fun f ->
                   if !proved then () 
                   else
                     let l = derived_rule_pos gamma seqlist' f tbl in
                     List.iter 
                       (fun x ->
                          saturated := insert_data x sequent && !saturated) l)
                sub_pos;
              Set_formula.iter
                (fun f ->
                   if !proved then ()
                   else
                     let l = derived_rule_theta theta seqlist' f tbl in
                     List.iter
                       (fun x ->
                          saturated := insert_data x sequent && !saturated) l)
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
  | Async (theta, gamma, l) -> begin match l with
      | [] ->
          let map = 
            List.fold_left 
              (fun res f -> insert f res)
              Map_formula.empty gamma in
          prove (theta, map)
      | hd :: tl -> begin match hd with
          | With (f, g) -> 
              prove_general (Async (theta, gamma, f :: tl));
              if !proved then begin
                proved := false;
                database := Set_sequent.empty;
                prove_general (Async (theta, gamma, g :: tl)) end
          | Par (f, g) -> 
              prove_general (Async (theta, gamma, g :: f :: tl))
          | Top -> 
              proved := true
          | Bottom ->
              prove_general (Async (theta, gamma, tl))
          | Whynot f ->
              prove_general (Async (Set_formula.add f theta, gamma, tl))
          | _ -> prove_general (Async (theta, hd :: gamma, tl)) end end
  | Sync _ -> assert false

let prove_sequent sequent nb_copies = 
  let t = Sys.time () in
  proved := false;
  max_nb_copies := nb_copies;
  prove_general sequent;
  let exec_time = Sys.time () -. t in
  if !proved then (Some true, None, exec_time) else (None, None, exec_time)
