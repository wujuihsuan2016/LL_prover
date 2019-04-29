(*** Backward proof search in LL (LLF) ***)

open Lexer
open Parser
open Lexing
open Formula
open Printer 
open Format
open Fctns

(* [bl] indicates if the (pseudo-)bound on the number of applications of the D2
   rule is reached. *)
let bl = ref false 

(* [sort_whynot l] sorts the list of formulas [l] in ascending order using
   [whynot_height f] as the key of [f]. *)
let sort_whynot l =
  List.sort (fun x y -> whynot_height y - whynot_height x) l 

(* [prove sequent select_d2 max_d2] attempts to prove the sequent [sequent]
   where [select_d2] contains the candidates for the D2 rule and [max_d2]
   is a (pseudo-)bound on the number of applications of the D2 rule. *)
let rec prove sequent select_d2 max_d2 = match sequent with
  | Async (theta, gamma, l) -> begin match l with
      | [] ->
          let rec apply_d1 k =
            if k = List.length gamma then None
            else
              let f, gamma' = choose_kth_from_list k gamma in 
              if is_neg f then apply_d1 (k + 1)
              else 
                try 
                  let p = get_op (prove (Sync (theta, gamma', f)) select_d2 max_d2) in
                  Some (Node (sequent, D1 (f, gamma'), [p]))
                with NoValue -> apply_d1 (k + 1) in 
          begin try
            Some (get_op (apply_d1 0)) 
          with NoValue ->
            let rec apply_d2 select_d2 max_d2 =
              let f = List.hd select_d2 in
              try
                let p = 
                  get_op (prove (Sync (theta, gamma, f)) 
                    (List.tl select_d2) max_d2) in
                Some (Node (sequent, D2 f, [p]))
              with NoValue ->
                apply_d2' (List.tl select_d2) max_d2 
            and apply_d2' select_d2 max_d2 = 
              if select_d2 = [] then begin
                (if max_d2 = 0 then (bl := true; raise NoValue));                    
                let select_d2' = 
                  sort_whynot (List.filter (fun x -> not (is_neg x)) 
                  (Set_formula.elements theta)) in
                if select_d2' = [] then None
                else
                  apply_d2 select_d2' (max_d2 - 1) end
              else
                apply_d2 select_d2 max_d2 
            in
            begin try 
              if Set_formula.for_all is_neg theta then None
              else 
                Some (get_op (apply_d2' select_d2 max_d2))
            with NoValue -> None end end 
      | hd :: tl ->
          begin match hd with 
          | Bottom -> 
              begin try
                let p = get_op (prove (Async (theta, gamma, tl)) select_d2 max_d2) in
                Some (Node (sequent, Bottom_intro, [p]))
              with NoValue -> None end 
          | Top -> Some (Node (sequent, Top_intro, [Null]))
          | With (f, g) ->  
              if whynot_height f > whynot_height g then
                try 
                  let pg = get_op (prove (Async (theta, gamma, g :: tl)) select_d2 max_d2) in
                  let pf = get_op (prove (Async (theta, gamma, f :: tl)) select_d2 max_d2) in
                  Some (Node (sequent, With_intro, [pf; pg]))
                with NoValue -> None
              else
                begin try 
                  let pf = get_op (prove (Async (theta, gamma, f :: tl)) select_d2 max_d2) in
                  let pg = get_op (prove (Async (theta, gamma, g :: tl)) select_d2 max_d2) in
                  Some (Node (sequent, With_intro, [pf; pg]))
              with NoValue -> None end 
          | Par (f, g) ->
              begin try 
                let p = get_op (prove (Async (theta, gamma, g :: f :: tl)) select_d2 max_d2) in
                Some (Node (sequent, Par_intro, [p]))
              with NoValue -> None end
          | Whynot g ->
              begin try
                let p = 
                  get_op 
                    (prove (Async (Set_formula.add g theta, gamma, tl))
                    select_d2 max_d2) in
                Some (Node (sequent, Whynot_intro, [p]))
              with NoValue ->
                None end
          | _ ->
              try 
                let p = get_op (prove (Async (theta, hd :: gamma, tl)) select_d2 max_d2) in
                Some (Node (sequent, R_async, [p]))
              with NoValue -> None 
           end end   
  | Sync (theta, gamma, f) -> 
      match f with
      | _ when is_async f || is_neg f -> 
          begin try 
            let p = get_op (prove (Async (theta, gamma, [f])) select_d2 max_d2) in
            Some (Node (sequent, R_sync, [p]))
          with NoValue -> None end
      | One ->
          if List.length gamma = 0 then 
            Some (Node (sequent, One_intro, [Null]))
          else 
            None
      | Plus (g, h) -> 
          if whynot_height g > whynot_height h then
            try 
              let p = get_op (prove (Sync (theta, gamma, h)) select_d2 max_d2) in
              Some (Node (sequent, Plus_intro_2, [p]))
            with NoValue -> 
              try
                let p = get_op (prove (Sync (theta, gamma, g)) select_d2 max_d2) in
                Some (Node (sequent, Plus_intro_1, [p]))
              with NoValue -> None 
          else
            begin try 
              let p = get_op (prove (Sync (theta, gamma, g)) select_d2 max_d2) in
              Some (Node (sequent, Plus_intro_1, [p]))
            with NoValue -> 
              try
                let p = get_op (prove (Sync (theta, gamma, h)) select_d2 max_d2) in
                Some (Node (sequent, Plus_intro_2, [p]))
              with NoValue -> None end 
      | Tensor (g, h) ->
          let rec split_gamma k = 
            if k = -1 then None
            else
              let gamma1, gamma2 = split_list gamma k in
              try
                if whynot_height g > whynot_height h then
                  let ph = 
                    get_op (prove (Sync (theta, gamma2, h)) select_d2 max_d2) in
                  let pg = 
                    get_op (prove (Sync (theta, gamma1, g)) select_d2 max_d2) in
                  Some (Node (sequent, Tensor_intro (gamma1, gamma2), [pg; ph]))
                else
                  let pg = 
                    get_op (prove (Sync (theta, gamma1, g)) select_d2 max_d2) in
                  let ph = 
                    get_op (prove (Sync (theta, gamma2, h)) select_d2 max_d2) in
                  Some (Node (sequent, Tensor_intro (gamma1, gamma2), [pg; ph]))
              with NoValue ->
                split_gamma (k - 1) in
          let k = fast_exp_2 (List.length gamma) - 1 in
          split_gamma k
      | OfCourse g ->
          if gamma = [] then
            try 
              let p = get_op (prove (Async (theta, gamma, [g])) select_d2 max_d2) in
              Some (Node (sequent, OfCourse_intro, [p]))
            with NoValue -> None
          else
            None
      | Pos atom -> 
          if gamma = [Neg atom] then 
            Some (Node (sequent, I1, [Null]))
          else
            if gamma = [] && Set_formula.mem (Neg atom) theta then
              Some (Node (sequent, I2, [Null]))
            else
              None
      | _ -> None  

(* [prove_sequent sequent cst_max_d2] attempts to prove [sequent] and returns
   the result [(res, proof, time)].
   [res] = None if the bound [cst_max_d2] is reached, and [res] = (Some b)
   when the proof search has been finished and b indicates the provability of
   [sequent]. When the sequent is provable, [proof] contains the proof found.
   *)
let prove_sequent sequent cst_max_d2 = 
  bl := false;
  let t = Sys.time () in
  match prove sequent [] cst_max_d2 with
    | None ->
        let exec_time = Sys.time () -. t in
        if !bl then (None, None, exec_time)
        else
          (Some false, None, exec_time)
    | Some proof -> 
        let exec_time = Sys.time () -. t in
        (Some true, Some proof, exec_time)
