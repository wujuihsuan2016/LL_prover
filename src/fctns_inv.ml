(*** Functions for the inverse method ***)

open Formula
open Fctns

(** Definition of contexts **)

module Map_formula = Map.Make(struct type t = formula let compare = compare end)

(* We use [map_formula] to represent multisets of formulas *)
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

(** Some functions for linear contexts **)

(* [find_opt f m] returns the multiplicity of [f] in [m]. *)
let find_opt x map = 
  try
    Some (Map_formula.find x map)
  with Not_found -> None 

(* [mem_map f m] checks if [f] occurs in [m]. *)
let mem_map x map = not (find_opt x map = None || find_opt x map = Some 0)

(* [is_empty m] checks if [m] is empty. *)
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

(* [card gamma] returns the cardinal of the linear context [gamma]. *) 
let card gamma = 
  List.fold_left (fun res (_, n) -> res + n) 0 (Map_formula.bindings gamma) 

(* [concat gamma1 gamma2] returns the concatenation of the two linear contexts
   [gamma1] and [gamma2]. *)
let concat gamma1 gamma2 = 
  union (+) gamma1 gamma2

(* [map_map f gamma] applies the function [f] to the elements [a1], ... , [an]
   of [gamma] and returns the context [f a1, f a2, ... , f an]. *)
let map_map f gamma = 
  List.fold_left 
    (fun res (g, i) -> Map_formula.add (f g) i res)
      Map_formula.empty (Map_formula.bindings gamma)

exception Map_error

(* [inclusion gamma1 gamma2] checks if [gamma1] is included in [gamma2]. *)
let inclusion gamma1 gamma2 =
  List.fold_left 
    (fun res (x, n) -> 
       try res && (Map_formula.find x gamma2 - n >= 0) with Not_found -> n = 0
         || false)
    true (Map_formula.bindings gamma1)

(* [inclusion gamma1 gamma2] checks if [gamma1] is equal to [gamma2]. *)
let eq_map gamma1 gamma2 =
  inclusion gamma1 gamma2 && inclusion gamma2 gamma1

(* [diff gamma1 gamma2] returns [gamma1] - [gamma2] if [gamma2] if included in
   [gamma1]. Otherwise, the exception Map_error is raised. *)
let diff gamma1 gamma2 =
  (if not (inclusion gamma2 gamma1) then raise Map_error);
  List.fold_left 
    (fun res (x, n) -> 
      Map_formula.add x 
      (n - (try Map_formula.find x gamma2 with Not_found -> 0)) res)
    Map_formula.empty (Map_formula.bindings gamma1)

(* [lub gamma1 gamma2] returns the least upper bound of [gamma1] and [gamma2].
   *)
let lub gamma1 gamma2 = 
  union max gamma1 gamma2

let split_map l map = 
  List.fold_left 
    (fun (map1, map2) (x, n) -> 
       Map_formula.add x n map1, Map_formula.add x (Map_formula.find x map - n)
       map2) (Map_formula.empty, Map_formula.empty) l

(* [insert x gamma] returns a linear context obtained from [gamma] by inserting
   the formula [x]. *)
let insert x gamma =
  concat (Map_formula.singleton x 1) gamma

exception ContextError

(* [simp_ctxt ctxt] returns a simplified context obtained from [ctxt]. *)
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

