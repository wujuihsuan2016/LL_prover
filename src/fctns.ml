(*** Some useful functions ***)

open Formula

(** Basic functions on formulas **)

(* [is_async f] checks if [f] is asynchronous. *)
let is_async = function
  | With _ | Par _ | Top | Bottom | Whynot _ -> true
  | _ -> false

(* [is_neg f] checks if [f] is a negative atom. *)
let is_neg = function
  | Neg _ -> true
  | _ -> false

(* [is_atom f] checks if [f] is an atom. *)
let is_atom = function
  | Pos _ | Neg _ -> true
  | _ -> false 

(* [is_atom f] checks if the top-level connective of [f] is binary. *)
let is_binop = function
  | Tensor _ | Plus _ | With _ | Par _ | Impl _ -> true
  | _ -> false 

(* [left_sync f] checks if [f] is left-synchronous (for ILLF). *)
let left_sync = function
  | With _ | Top | Impl _ | Pos _ -> true
  | _ -> false

(* [right_sync f] checks if [f] is right-synchronous (for ILLF). *)
let right_sync = function
  | Tensor _ | Zero | One | OfCourse _ | Pos _ | Plus _ -> true
  | _ -> false

(* [left_async f] checks if [f] is left-asynchronous (for ILLF). *)
let left_async = function
  | Tensor _ | Zero | One | OfCourse _ | Plus _ -> true
  | _ -> false

(* [right_async f] checks if [f] is right-asynchronous (for ILLF). *)
let right_async = function
  | With _ | Top | Impl _ -> true
  | _ -> false

(* [size f] returns the size of [f]. *)
let rec size = function
  | Pos _ | Neg _ | One | Zero | Top | Bottom -> 1
  | OfCourse f | Whynot f -> size f + 1
  | Tensor (f, g) | Plus (f, g) | With (f, g) | Par (f, g) | Impl (f, g) -> 
      size f + size g + 1

(* [whynot_height f] returns the whynot-height of [f]. *)
let rec whynot_height = function
  | Pos _ | Neg _ | One | Zero | Top | Bottom -> 0
  | OfCourse f -> whynot_height f
  | Whynot f -> whynot_height f + 1
  | Tensor (f, g) | Plus (f, g) | With (f, g) | Par (f, g) | Impl (f, g) ->
      max (whynot_height f) (whynot_height g)

(* [free_variables f] returns the set of free variables of [f]. *)
let rec free_variables = function
  | Pos x | Neg x -> Set_var.of_list [x]
  | One | Zero | Top | Bottom -> Set_var.empty
  | OfCourse f | Whynot f -> free_variables f
  | Tensor (f, g) | Par (f, g) | Plus (f, g) | With (f, g) | Impl (f, g) ->
      Set_var.union (free_variables f) (free_variables g)

(* [neg_formula f] returns the negation/dual of [f]. *)
let rec neg_formula = function
  | Pos x -> Neg x
  | Neg x -> Pos x
  | One -> Bottom
  | Zero -> Top
  | Top -> Zero
  | Bottom -> One
  | OfCourse f -> Whynot (neg_formula f)
  | Whynot f -> OfCourse (neg_formula f)
  | Tensor (f, g) -> Par (neg_formula f, neg_formula g)
  | Par (f, g) -> Tensor (neg_formula f, neg_formula g)
  | Plus (f, g) -> With (neg_formula f, neg_formula g)
  | With (f, g) -> Plus (neg_formula f, neg_formula g)
  | Impl (f, g) -> Tensor (rewrite f, neg_formula g)

(* [rewrite f] returns the "negation normal form" of [f]. A formula is in
   negation normal form if it contains no occurrence of -o and all negations
   have atomic scope. *)
and rewrite = function
  | Impl (f, g) -> Par (neg_formula f, rewrite g)
  | OfCourse f -> OfCourse (rewrite f)
  | Whynot f -> Whynot (rewrite f)
  | Tensor (f, g) -> Tensor (rewrite f, rewrite g)
  | Par (f, g) -> Par (rewrite f, rewrite g)
  | Plus (f, g) -> Plus (rewrite f, rewrite g)
  | With (f, g) -> With (rewrite f, rewrite g)
  | f -> f

(* [string_of_formula f] returns the representation of the formula [f] in
   the Yalla library of Coq. *)
let rec string_of_formula = function
  | Pos x -> x
  | Neg x -> "(dual " ^ x ^ ")"
  | One -> "one"
  | Zero -> "zero"
  | Top -> "top"
  | Bottom -> "bot"
  | OfCourse f ->
      let s = string_of_formula f in
      "(oc " ^ s ^ ")"
  | Whynot f ->
      let s = string_of_formula f in
      "(wn " ^ s ^ ")"
  | Tensor (f, g) ->
      let sf = string_of_formula f in
      let sg = string_of_formula g in
      "(tens " ^ sf ^ " " ^ sg ^ ")"
  | Par (f, g) ->
      let sf = string_of_formula f in
      let sg = string_of_formula g in
      "(parr " ^ sf ^ " " ^ sg ^ ")"
  | Plus (f, g) ->
      let sf = string_of_formula f in
      let sg = string_of_formula g in
      "(aplus " ^ sf ^ " " ^ sg ^ ")"
  | With (f, g) ->
      let sf = string_of_formula f in
      let sg = string_of_formula g in
      "(awith " ^ sf ^ " " ^ sg ^ ")"
  | Impl (f, g) ->
      assert false

let string_of_flist l =
  let rec string_of_list = function
    | [] -> ""
    | [x] -> string_of_formula x
    | hd :: tl -> (string_of_formula hd) ^ "; " ^ (string_of_list tl)
  in "[" ^ string_of_list l ^ "]"

(** Functions for manipulating LLF sequents **)

let get_list = function
  | Async (_, _, l) -> l
  | Sync (_, _, f) -> [f] 
 
let get_theta = function
  | Async (th, _, _) -> th
  | Sync (th, _, _) -> th

let get_gamma = function
  | Async (_, ga, _) -> ga
  | Sync (_, ga, _) -> ga 

let map_wn = List.map (fun x -> Whynot x) 

(** Manipulation of the type ['a option] **)

exception NoValue

let get_op = function
  | Some x -> x 
  | None -> raise NoValue

let is_some = function
  | Some _ -> true
  | None -> false 

let inclusion_op opt1 opt2 = match (opt1, opt2) with
  | None, _ -> true
  | Some x, Some y -> x = y
  | _-> false

(** Manipulation of sets of formulas **)

let eq_set s1 s2 = Set_formula.elements s1 = Set_formula.elements s2

let inclusion_set s1 s2 = Set_formula.is_empty (Set_formula.diff s1 s2)

(** Functions for splitting contexts **)

let rec split_list_aux (acc1, acc2) l k = match l with
  | [] -> acc1, acc2
  | hd :: tl -> 
      if k mod 2 = 0 then split_list_aux (acc1, hd :: acc2) tl (k / 2)
      else split_list_aux (hd :: acc1, acc2) tl (k / 2)

let split_list l k =
  split_list_aux ([], []) l k

let choose_from_list m l k =
  let rec aux_choose acc l k = match l with
    | [] -> acc
    | hd :: tl ->
        let acc' = List.init (k mod m) (fun _ -> hd) @ acc in
        aux_choose acc' tl (k / m) in
  aux_choose [] l k

let rec generate_sublist k m l a b =
  let rec cut k l = match k with
    | 0 -> [], List.hd l, List.tl l
    | _ -> 
        let l1, x, l2 = cut (k-1) (List.tl l) in
        List.hd l :: l1, x, l2
  in 
  let l1, x, l2 = cut k l in
  let l1' = choose_from_list m l1 a in
  let l2' = choose_from_list (m + 1) l2 b in
  List.init m (fun _ -> x) @ l1' @ l2' 

let rec fast_exp_aux acc m k =
    if k = 0 then acc
    else 
      if k = 1 then m * acc
      else
        if k mod 2 = 1 then 
          fast_exp_aux (acc * m) (m*m) (k / 2)
        else
          fast_exp_aux acc (m*m) (k/2)

let fast_exp_2 k =
  fast_exp_aux 1 2 k      

let fast_exp m k = 
  fast_exp_aux 1 m k

let rec choose_kth_from_list k l = match l with
  | [] -> assert false
  | [x] -> x, []
  | hd :: tl ->
      if k = 0 then hd, tl
      else
        let x, tl' = choose_kth_from_list (k - 1) tl in
        x, hd :: tl'

let map_product f l1 l2 = 
  let rec map_product_aux acc l1 l2 = match l1  with
    | [] -> acc
    | hd :: tl -> map_product_aux (List.map (f hd) l2 @ acc) tl l2
  in map_product_aux [] l1 l2

let map_flat_product f l1 l2 = 
  let rec map_flat_product_aux acc l1 l2 = match l1 with
    | [] -> acc
    | hd :: tl -> 
        map_flat_product_aux (List.concat (List.map (f hd) l2) @ acc) tl l2
  in map_flat_product_aux [] l1 l2
  
(** Manipulation of ILL sequents **)

let ill_get_theta = function
  | R_focal (th, _, _) -> th
  | L_focal (th, _, _, _) -> th
  | Active (th, _, _, _) -> th

let ill_get_gamma = function
  | R_focal (_, ga, _) -> ga
  | L_focal (_, ga, f, _) -> f :: ga
  | Active (_, ga, om, _) -> om @ ga 

let ill_get_formula = function
  | R_focal (_, _, f) -> f
  | L_focal (_, _, _, f) -> f
  | Active (_, _, _, f) -> f 

let ill_get_seq seq =
  ill_get_theta seq, ill_get_gamma seq, ill_get_formula seq

let map_oc' = List.map (fun f -> OfCourse f)

let map_oc theta = map_oc' (Set_formula.elements theta)

(* [sub_formulas f] returns the set of subformulas of [f]. *)
let rec sub_formulas formula = match formula with
  | Tensor (f, g) | Plus (f, g) | With (f, g) | Par (f, g) | Impl (f, g) -> 
      Set_formula.add formula 
        (Set_formula.union (sub_formulas f) (sub_formulas g))
  | OfCourse f | Whynot f -> Set_formula.add formula (sub_formulas f)
  | _ -> Set_formula.singleton formula

(* [sub_formulas_l l] returns the set of subformulas of formulas in [l]. *)
let sub_formulas_l l = 
  List.fold_left 
    (fun res f -> Set_formula.union res (sub_formulas f)) 
       Set_formula.empty l

let rec check_theta' x f = match f with
  | Tensor (g, h) | Plus (g, h) | With (g, h) | Par (g, h) | Impl (g, h) ->
      x <> g && x <> h && check_theta' x g && check_theta' x h
  | OfCourse g -> 
      if x = g then true
      else check_theta' x g
  | Whynot g ->
      x <> g && check_theta' x g
  | _ -> true

(* [check_theta x f] check if all occurrences of [x] in [f] are in the form of
   [!x]. *)
let check_theta x f = x <> f && check_theta' x f

(* [check_theta_ll' x x^ f] checks if all occurrences of [x] and [x^] in [f]
   are in the form of [!x] or [?x^] *)
let rec check_theta_ll' x neg_x f = match f with
  | Impl _ -> assert false 
  | Tensor (g, h) | Plus (g, h) | With (g, h) | Par (g, h) ->
      x <> g && x <> h && neg_x <> g && neg_x <> h && 
      check_theta_ll' x neg_x g && check_theta_ll' x neg_x h
  | OfCourse g ->
      if x = g then true 
      else
        if neg_x = g then false
        else check_theta_ll' x neg_x g
  | Whynot g ->
      if x = g then false
      else
        if neg_x = g then true
        else check_theta_ll' x neg_x g
  | _ -> true

let check_theta_ll x neg_x f = 
  x <> f && neg_x <> f && check_theta_ll' x neg_x f

(** Manipulation of files **)

let rec create dir =
  try
    Unix.mkdir dir 0o777 
  with 
    | Unix.Unix_error (EEXIST, _, _) -> ()
    | Unix.Unix_error (ENOENT, _, _) ->   
        let dir' = Filename.dirname dir in
        create dir';
        Unix.mkdir dir 0o777;
    | _ -> assert false

let open_out filename =
  try Pervasives.open_out filename with _ ->
    let dir = Filename.dirname filename in
    create dir;
    Pervasives.open_out filename

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

(* [suffix l] computes the list of suffixes of [l]. *)
let rec suffix = function
  | [] -> [[]]
  | hd :: tl ->
      (hd :: tl) :: (suffix tl)
