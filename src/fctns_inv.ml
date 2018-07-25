open Formula
open Fctns

module Map_formula = Map.Make(struct type t = formula let compare = compare end)

type map_formula = int Map_formula.t

type context = 
  | Weight of bool * map_formula
  | Concat of context * map_formula
  | CPlus of context * context
  | CTimes of context * context

let map_to_list gamma = 
  List.fold_left 
    (fun res (x, n) -> (Array.to_list (Array.make n x)) @ res) 
    [] (Map_formula.bindings gamma)

(* Some functions for linear contexts *)

let find_opt x map = 
  try
    Some (Map_formula.find x map)
  with Not_found -> None 

let mem_map x map = not (find_opt x map = None || find_opt x map = Some 0)

let is_empty map =
  List.for_all (fun (_, n) -> n = 0) (Map_formula.bindings map) 

let union f map1 map2 =
  let keys1 = Set_formula.of_list (List.map fst (Map_formula.bindings map1)) in
  let keys2 = Set_formula.of_list (List.map fst (Map_formula.bindings map2)) in
  let keys = Set_formula.union keys1 keys2 in
  let map = ref Map_formula.empty in
  Set_formula.iter 
    (fun x ->
       match (find_opt x map1, find_opt x map2) with
         | None, None -> () 
         | None, Some v -> map := Map_formula.add x v !map
         | Some v, None -> map := Map_formula.add x v !map
         | Some v1, Some v2 -> map := Map_formula.add x (f v1 v2) !map)
    keys;
  !map
    
let card gamma = 
  List.fold_left (fun res (_, n) -> res + n) 0 (Map_formula.bindings gamma) 

let concat gamma1 gamma2 = 
  union (+) gamma1 gamma2

let map_map f gamma = 
  List.fold_left 
    (fun res (g, i) -> Map_formula.add (f g) i res)
      Map_formula.empty (Map_formula.bindings gamma)

exception Map_error

let inclusion gamma1 gamma2 =
  List.fold_left 
    (fun res (x, n) -> 
       try res && (Map_formula.find x gamma2 - n >= 0) with Not_found -> n = 0
         || false)
    true (Map_formula.bindings gamma1)

let eq_map gamma1 gamma2 =
  inclusion gamma1 gamma2 && inclusion gamma2 gamma1

let diff gamma1 gamma2 =
  (if not (inclusion gamma2 gamma1) then raise Map_error);
  List.fold_left 
    (fun res (x, n) -> 
      Map_formula.add x 
      (n - (try Map_formula.find x gamma2 with Not_found -> 0)) res)
    Map_formula.empty (Map_formula.bindings gamma1)

(* least upper bound *)    
let lub gamma1 gamma2 = 
  union max gamma1 gamma2

let split_map l map = 
  List.fold_left 
    (fun (map1, map2) (x, n) -> 
       Map_formula.add x n map1, Map_formula.add x (Map_formula.find x map - n)
       map2) (Map_formula.empty, Map_formula.empty) l
  
let insert x gamma =
  concat (Map_formula.singleton x 1) gamma

exception ContextError

let rec simp_ctxt = function
  | Concat (ctxt, x) -> 
      let [@warning "-8"] Weight (w, gamma) = simp_ctxt ctxt in
      Weight (w, concat x gamma)
  | CPlus (ctxt, ctxt') ->
      let [@warning "-8"] Weight (w, gamma) = simp_ctxt ctxt in
      let [@warning "-8"] Weight (w', gamma') = simp_ctxt ctxt' in
      begin match (w, w') with
        | false, false -> 
            if eq_map gamma gamma' then ctxt else raise ContextError 
        | false, true ->  
            if inclusion gamma' gamma then ctxt else raise ContextError
        | true, false ->  
            if inclusion gamma gamma' then ctxt' else raise ContextError
        | true, true -> Weight (true, lub gamma gamma') end
  | CTimes (ctxt, ctxt') ->
      let [@warning "-8"] Weight (w, gamma) = simp_ctxt ctxt in
      let [@warning "-8"] Weight (w', gamma') = simp_ctxt ctxt' in
      Weight (w || w', concat gamma gamma')        
  | x -> x

