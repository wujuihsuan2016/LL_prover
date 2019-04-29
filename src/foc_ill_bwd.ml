(*** Backward proof search in ILL (ILLF) ***)

open Formula
open Fctns
open Printer

(* [cst_max_copy] is the (pseudo-)bound on the number of applications of the copy
   rule. *)
let cst_max_copy = 4

(* [bl] indicates if [cst_max_copy] is reached. *)
let bl = ref false

(* [get_atoms f] returns the set of atoms in [f]. When a negative atom is found,
   we store its corresponding positive atom instead. *)
let rec get_atoms = function
  | Tensor (f, g) | Plus (f, g) | With (f, g) | Par (f, g) | Impl (f, g) ->
      Set_formula.union (get_atoms f) (get_atoms g)
  | OfCourse f | Whynot f -> get_atoms f
  | Neg x | Pos x -> Set_formula.singleton (Pos x)
  | _ -> Set_formula.empty

(* [get_atoms_sequent sequent] returns the set of atoms in [sequent]. *)
let get_atoms_sequent sequent = 
  let l = match sequent with
    | Active (theta, gamma, omega, f) -> 
        f :: omega @ gamma @ (Set_formula.elements theta)
    | R_focal (theta, gamma, f) ->
        f :: gamma @ (Set_formula.elements theta)
    | L_focal (theta, gamma, f, g) -> 
        g :: g :: gamma @ (Set_formula.elements theta) in
  List.fold_left 
    (fun res f -> Set_formula.union res (get_atoms f)) Set_formula.empty l

(* [prove sequent select_copy max_copy] attempts to prove the sequent [sequent]
   where [select_copy] contains the candidates for the Copy rule and [max_copy]
   is a (pseudo-)bound on the number of applications of the Copy rule. *)
let rec prove sequent select_copy max_copy =  
  match sequent with
    | R_focal (theta, gamma, f) -> begin match f with
        | Tensor (g, h) ->
            let rec split_gamma k = 
              if k = -1 then None
              else
                let gamma1, gamma2 = split_list gamma k in
                try
                  if size g > size h then
                    let ph = 
                      get_op 
                        (prove (R_focal (theta, gamma2, h)) select_copy 
                         max_copy) 
                    in
                    let pg = 
                      get_op 
                        (prove (R_focal (theta, gamma1, g)) select_copy 
                         max_copy) 
                    in
                    Some (INode (sequent, Tensor_R (gamma1, gamma2), [pg; ph]))
                  else
                    let pg = 
                      get_op 
                        (prove (R_focal (theta, gamma1, g)) select_copy
                         max_copy)  
                    in
                    let ph =
                      get_op 
                        (prove (R_focal (theta, gamma2, h)) select_copy 
                         max_copy) in
                    Some (INode (sequent, Tensor_R (gamma1, gamma2), [pg; ph]))
                with NoValue ->
                  split_gamma (k - 1) in
            let k = fast_exp_2 (List.length gamma) - 1 in
            split_gamma k
        | Plus (g, h) -> begin
            try
              let pg = 
                get_op (prove (R_focal (theta, gamma, g)) select_copy max_copy)
              in
              Some (INode (sequent, Plus_R_1, [pg]))
            with NoValue -> begin
              try 
                let ph =
                  get_op 
                    (prove (R_focal (theta, gamma, h)) select_copy max_copy) in
              Some (INode (sequent, Plus_R_2, [ph]))
              with NoValue -> None end end
        | One -> 
            if gamma = [] then
              Some (INode (sequent, One_R, [INull]))
            else None
        | OfCourse g ->
            if gamma = [] then
              try 
                let p = 
                  get_op (prove (Active (theta, [], [], g)) select_copy max_copy) 
                in
                Some (INode (sequent, OfCourse_R, [p])) 
              with NoValue -> None
            else
              None
        | Pos _ -> begin 
            try 
              let p = 
                get_op 
                  (prove (Active (theta, gamma, [], f)) select_copy max_copy) 
              in
              Some (INode (sequent, Rb_, [p])) 
            with NoValue -> None end
        | _  when right_async f -> begin
            try
              let p = 
                get_op (prove (Active (theta, gamma, [], f)) select_copy max_copy) 
              in
              Some (INode (sequent, Rb, [p]))
            with NoValue -> None end
        | _ -> None end
    | L_focal (theta, gamma, f, g) -> begin match f with
        | Pos _ ->
            if gamma = [] && g = f then
              Some (INode (sequent, Init, [INull]))
            else
              if left_async f then
                try
                  let p = 
                    get_op 
                      (prove (Active (theta, gamma, [f], g)) select_copy max_copy) 
                  in
                  Some (INode (sequent, Lb, [p])) 
                with NoValue -> None 
              else 
                None
        | With (h, k) -> begin 
            try 
              let ph = 
                get_op (prove (L_focal (theta, gamma, h, g)) select_copy max_copy) 
              in
              Some (INode (sequent, With_L_1, [ph]))
            with NoValue -> begin
              try 
                let pk = 
                  get_op 
                    (prove (L_focal (theta, gamma, k, g)) select_copy max_copy) 
                in
                Some (INode (sequent, With_L_2, [pk]))
              with NoValue -> None end end
        | Impl (h, h') ->
            let rec split_gamma k = 
              if k = -1 then None
              else
                let gamma1, gamma2 = split_list gamma k in
                try 
                  let ph = 
                    get_op 
                      (prove (R_focal (theta, gamma1, h)) select_copy max_copy) 
                  in
                  let ph' =
                    get_op 
                      (prove (L_focal (theta, gamma2, h', g)) select_copy 
                       max_copy) 
                  in
                  Some (INode (sequent, Impl_L (gamma1, gamma2), [ph; ph']))
                with NoValue -> split_gamma (k - 1) in
            let k = fast_exp_2 (List.length gamma) - 1 in
            split_gamma k 
        | _ when right_sync g && left_async f -> begin 
            try
              let p = 
                get_op 
                  (prove (Active (theta, gamma, [f], g)) select_copy max_copy) 
              in
              Some (INode (sequent, Lb, [p])) 
            with NoValue -> None end 
        | _ -> None end
    | Active (theta, gamma, omega, f) -> match f with
        | With (g, h) -> begin
            try 
              let pg = 
                get_op 
                  (prove (Active (theta, gamma, omega, g)) select_copy max_copy) 
              in
              let ph = 
                get_op 
                  (prove (Active (theta, gamma, omega, h)) select_copy max_copy) 
              in
              Some (INode (sequent, With_R, [pg; ph]))
            with NoValue -> None end
        | Impl (g, h) -> begin
            try 
              let p = 
                get_op 
                  (prove (Active (theta, gamma, g :: omega, h)) 
                   select_copy max_copy) in
              Some (INode (sequent, Impl_R, [p]))
            with NoValue -> None end
        | Top -> Some (INode (sequent, Top_R, [INull]))
        | _ -> match omega with
            | [] ->
                let rec apply_lf k = 
                  if k = List.length gamma then None
                  else
                    let g, gamma' = choose_kth_from_list k gamma in
                    if not (left_sync g) then apply_lf (k + 1)
                    else
                      try
                        let p = 
                          get_op 
                            (prove (L_focal (theta, gamma', g, f))
                             select_copy max_copy) in
                        Some (INode (sequent, Lf, [p]))
                      with NoValue -> apply_lf (k + 1) in
                begin try
                  Some (get_op (apply_lf 0)) 
                with NoValue ->
                  let rec apply_copy select_copy max_copy updated = 
                    let g = List.hd select_copy in
                    try 
                      let p =
                        get_op 
                          (prove (L_focal (theta, gamma, g, f)) 
                          (List.tl select_copy) max_copy)        
                      in
                      Some (INode (sequent, Copy g, [p]))
                    with NoValue ->
                      apply_copy' (List.tl select_copy) max_copy updated
                  and apply_copy' select_copy max_copy updated =
                    if select_copy = [] then begin 
                      if updated then None
                      else begin
                        (if max_copy = 0 then (bl := true; raise NoValue));
                        let select_copy' = Set_formula.elements theta in
                        if select_copy' = [] then None
                        else
                          apply_copy select_copy' (max_copy - 1) true end end
                    else 
                      apply_copy select_copy max_copy updated
                  in
                  begin try
                    if Set_formula.is_empty theta
                      then raise NoValue
                    else
                      Some (get_op (apply_copy' select_copy max_copy false))
                  with NoValue -> 
                    if is_atom f then None
                    else begin
                      try 
                        let p = 
                          get_op 
                            (prove (R_focal (theta, gamma, f)) 
                             select_copy max_copy)
                        in
                        Some (INode (sequent, Rf, [p]))
                        with NoValue -> None end end end
            | hd :: tl -> match hd with
                | Tensor (g, h) -> begin 
                    try 
                      let p = 
                        get_op 
                          (prove (Active (theta, gamma, h :: g :: tl, f))
                           select_copy max_copy) in
                      Some (INode (sequent, Tensor_L, [p]))
                    with NoValue -> None end
                | Plus (g, h) -> begin
                    try
                      let pg = 
                        get_op 
                          (prove (Active (theta, gamma, g :: tl, f))
                           select_copy max_copy) in
                      let ph = 
                        get_op 
                          (prove (Active (theta, gamma, h :: tl, f)) 
                           select_copy max_copy) in 
                      Some (INode (sequent, Plus_L, [pg; ph]))
                    with NoValue -> None end
                | One -> begin
                    try 
                      let p =
                        get_op 
                          (prove (Active (theta, gamma, tl, f)) 
                           select_copy max_copy) in
                      Some (INode (sequent, One_L, [p]))
                    with NoValue -> None end
                | OfCourse g -> begin
                    try
                      let p = 
                        get_op 
                          (prove (Active (Set_formula.add g theta, gamma, tl, f))
                           select_copy max_copy) in
                      Some (INode (sequent, OfCourse_L, [p]))
                    with NoValue -> None end
                | Zero -> Some (INode (sequent, Zero_L, [INull]))
                | _ when left_sync hd -> begin 
                    try 
                      let p = 
                        get_op 
                          (prove (Active (theta, hd :: gamma, tl, f)) 
                           select_copy max_copy) in
                      Some (INode (sequent, Act, [p]))
                    with NoValue -> None end
                | _ -> None 

(* [prove_sequent sequent cst_max_copy] attempts to prove [sequent] and returns
   the result [(res, proof, time)].
   [res] = None if the bound [cst_max_copy] is reached, and [res] = (Some b)
   when the proof search has been finished and b indicates the provability of
   [sequent]. When the sequent is provable, [proof] contains the proof found.
   *)
let prove_sequent sequent cst_max_copy = 
  bl := false;
  let t = Sys.time () in
  let res = prove sequent [] cst_max_copy in
  match res, !bl with
    | None, false ->
        let exec_time = Sys.time () -. t in
        (Some false, None, exec_time)
    | None, true -> 
        let exec_time = Sys.time () -. t in
        (None, None, exec_time)
    | Some proof, _ -> 
        let exec_time = Sys.time () -. t in
        (Some true, Some proof, exec_time)
