
open Formula
open Fctns
open Printer

let tbl = Array.make 30 []
let rec insert_bin l1 l2 i = match l1 with
  | [] -> ()
  | hd1 :: tl1 ->
      List.iter 
        (fun x -> 
          tbl.(i) <- 
            [Tensor (hd1, x); Plus (hd1, x); Impl (hd1, x); With (hd1,
            x)] 
            @ tbl.(i)) l2; 
      insert_bin tl1 l2 i 

let rec create n =
  if tbl.(n-1) <> [] then ()
  else
    if n = 1 then 
      tbl.(0) <- [Top; One; Zero; Pos "X"; Pos "Y"]
    else begin
      create (n-1);
      List.iter (fun x -> tbl.(n-1) <- OfCourse x :: tbl.(n-1)) tbl.(n-2); 
      for i = 1 to (n-2) do begin
        insert_bin tbl.(i-1) tbl.(n-i-2) (n-1);
        end
      done;
      end

(* Statistics *)
let ll_statistics n =
  let provable, not_provable, others =
    ref 0, ref 0, ref 0 in
  create n;
  List.iter 
    (fun x -> 
       let sequent = Async (Set_formula.empty, [], [rewrite x]) in
       match Foc.prove_sequent sequent with
         | Some true -> incr provable
         | Some false -> incr not_provable
         | None -> incr others) tbl.(n-1);
  let ff = Format.std_formatter in
  print_str_line ff "Provability of formulas in LL";
  print_str_line ff ("Provable : " ^ string_of_int !provable);
  print_str_line ff ("Not provable : " ^ string_of_int !not_provable);
  print_str_line ff ("Unknown : " ^ string_of_int !others)

let ill_statistics n = 
  let provable, not_provable, others =
    ref 0, ref 0, ref 0 in
  create n;
  List.iter 
    (fun x -> 
       let sequent = Active (Set_formula.empty, [], [], x) in
       match Foc_ill.prove_sequent sequent with
         | Some true -> incr provable
         | Some false -> incr not_provable
         | _ -> incr others) tbl.(n-1);
  let ff = Format.std_formatter in
  print_str_line ff "Provability of formulas in ILL";
  print_str_line ff ("Provable : " ^ string_of_int !provable);
  print_str_line ff ("Not provable : " ^ string_of_int !not_provable);
  print_str_line ff ("Unknown : " ^ string_of_int !others)

let ll_ill_statistics n =
  let prov_prov, prov_nprov, prov_others, others_prov, others_nprov,
  others_others, nprov_prov, nprov_nprov, nprov_others = 
    ref 0, ref 0, ref 0, ref 0, ref 0, ref 0, ref 0, ref 0, ref 0 in
  create n;
  List.iter 
    (fun x -> 
      let ll_sequent = Async (Set_formula.empty, [], [rewrite x]) in
      let ill_sequent = Active (Set_formula.empty, [], [], x) in
      match Foc.prove_sequent ll_sequent, Foc_ill.prove_sequent ill_sequent with
        | Some true, Some true -> incr prov_prov
        | Some true, Some false -> incr prov_nprov
        | Some true, None -> incr prov_others
        | None, Some true -> incr others_prov
        | None, Some false -> incr others_nprov
        | None, None -> incr others_others 
        | Some false, Some true -> incr nprov_prov
        | Some false, Some false -> incr nprov_nprov 
        | Some false, None -> incr nprov_others) (tbl.(n-1));
  let ff = Format.std_formatter in
  print_str_line ff ("Provable in LL and in ILL : " ^ string_of_int !prov_prov);
  print_str_line ff 
    ("Provable in LL but not provable in ILL : " ^ string_of_int !prov_nprov);
  print_str_line ff
    ("Provable in LL but unknown in ILL : " ^ string_of_int !prov_others);
  print_str_line ff 
    ("Unknown in LL but provable in ILL : " ^ string_of_int !others_prov);
  print_str_line ff
    ("Unknown in LL but not provable in ILL : " ^ string_of_int !others_nprov);
  print_str_line ff
    ("Unknown in LL and in ILL : " ^ string_of_int !others_others);
  print_str_line ff 
    ("Not provable in LL but provable in ILL : " ^ string_of_int !nprov_prov);
  print_str_line ff 
    ("Not provable in LL and in ILL : " ^ string_of_int !nprov_nprov);
  print_str_line ff
    ("Not provable in LL but unknown in ILL : " ^ string_of_int !nprov_others)

let check_formula f = 
  let ll_sequent = Async (Set_formula.empty, [], [rewrite f]) in
  let ill_sequent = Active (Set_formula.empty, [], [], f) in
  match Foc.prove ll_sequent [] Foc.cst_max_d2 with
    | None -> false
    | Some _ -> match Foc_ill.prove_sequent ill_sequent with
        | Some false -> true
        | _ -> false 

(* Skeleton *)
type index = 
  | Index of int
  | Var of string 

type skeleton = 
  | STensor of bool (* polarity of the node *) * skeleton * skeleton
  | SPlus of bool * skeleton * skeleton 
  | SImpl of bool * skeleton * skeleton 
  | SWith of bool * skeleton * skeleton 
  | SOfCourse of bool * skeleton
  | SLeaf of bool * int 
  | STop of bool
  | SOne of bool
  | SZero of bool
  | SAtom of bool * int

let rec inv_polarity = function   
  | STensor (bl, x, y) -> STensor (not bl, inv_polarity x, inv_polarity y)
  | SPlus (bl, x, y) -> SPlus (not bl, inv_polarity x, inv_polarity y)
  | SImpl (bl, x, y) -> SImpl (not bl, inv_polarity x, inv_polarity y)
  | SWith (bl, x, y) -> SWith (not bl, inv_polarity x, inv_polarity y)
  | SOfCourse (bl, x) -> SOfCourse (not bl, inv_polarity x)
  | SLeaf (bl, i) -> SLeaf (not bl, i)  
  | STop bl -> STop (not bl)
  | SOne bl -> SOne (not bl)
  | SZero bl -> SZero (not bl)
  | SAtom (bl, name) -> SAtom (not bl, name) 

(* Check the implicative order of the given skeleton is >= k *)
let rec check_implicative_order k skel = match k with
  | 0 -> true
  | _ -> match skel with 
     | STensor (_, x, y) | SPlus (_, x, y) | SWith (_, x, y) -> 
      check_implicative_order k x || check_implicative_order k y
     | SImpl (_, x, y) ->
      check_implicative_order (k-1) x || check_implicative_order k y
     | SOfCourse (_, x) -> check_implicative_order k x
     | _ -> false  

let rec add_index k = function
  | STensor (bl, x, y) -> STensor (bl, add_index k x, add_index k y)
  | SPlus (bl, x, y) -> SPlus (bl, add_index k x, add_index k y)
  | SImpl (bl, x, y) -> SImpl (bl, add_index k x, add_index k y)
  | SWith (bl, x, y) -> SWith (bl, add_index k x, add_index k y)
  | SOfCourse (bl, x) -> SOfCourse (bl, add_index k x) 
  | SLeaf (bl, i) -> SLeaf (bl, i+k) 
  | _ -> assert false

let rec nb_leaves = function
  | STensor (_, x, y) | SPlus (_, x, y) | SImpl (_, x, y) | SWith (_, x, y) -> 
      nb_leaves x + nb_leaves y
  | SOfCourse (_, x) -> nb_leaves x
  | SLeaf _ -> 1
  | _ -> 1 

let tbl_skel : ((int * int), skeleton list) Hashtbl.t = Hashtbl.create 30  

let add_binop x y =
  let k = nb_leaves x in
  [STensor (true, x, add_index k y); SPlus (true, x, add_index k y); 
   SWith (true, x, add_index k y); SImpl (true, inv_polarity x, add_index k y)] 
       
let map_product f l1 l2 = 
  let rec map_product_aux l1 l2 acc = match l1 with
    | [] -> acc 
    | hd :: tl ->
        map_product_aux tl l2 (List.concat (List.map (f hd) l2) @ acc)
  in map_product_aux l1 l2 []   

let rec generate_skeletons n m =
  try Hashtbl.find tbl_skel (n, m) 
  with Not_found -> match (n, m) with
    | (i, j) when i < 0 || j < 0 -> []  
    | (0, 0) -> Hashtbl.add tbl_skel (0, 0) [SLeaf (true, 0)]; [SLeaf (true, 0)]
    | _ -> 
        let tmp = ref [] in
        for i = 0 to n-1 do
          for j = 0 to m do
            tmp := 
              (map_product add_binop 
                (generate_skeletons i j) (generate_skeletons (n-1-i) (m-j))) @
              !tmp;
          done;
        done;
        List.iter 
          (fun x -> 
             tmp := SOfCourse (true, x) :: !tmp) (generate_skeletons n (m-1));
        Hashtbl.add tbl_skel (n, m) !tmp;
        !tmp

let rec generate_skeletons2 n m = 
  try Hashtbl.find tbl_skel (n, m) 
  with Not_found -> match (n, m) with 
    | (i, j) when i < 0 || j < 0 -> []  
    | _ -> 
        for i = 0 to n do 
          for j = 0 to m do
            if (i, j) = (0, 0) then Hashtbl.add tbl_skel (0,0) [SLeaf (true, 0)]
            else 
              begin 
              let tmp = ref [] in
              for k = 0 to i-1 do
                for l = 0 to j do
                  tmp := 
                    map_product add_binop 
                      (Hashtbl.find tbl_skel (k, l)) 
                      (Hashtbl.find tbl_skel (i-1-k, j-l)) @ !tmp
                done;
              done;
              (if j > 0 then
                List.iter 
                  (fun x ->
                    tmp := SOfCourse (true, x) :: !tmp) 
                  (Hashtbl.find tbl_skel (i, j-1)));
              Hashtbl.add tbl_skel (i, j) !tmp;
              end
        done;
      done;
      Hashtbl.find tbl_skel (n,m)

(* Determine if a formula is !-like *)
let rec is_oc_like = function
  | SLeaf _  -> false 
  | STensor (_, x, y) | SPlus (_, x, y) -> is_oc_like x && is_oc_like y
  | SWith (_, x, y) -> 
      is_oc_like x || is_oc_like y
  | SOfCourse (_, x) -> true 
  | _ -> false

(* Determine if a formula contains a negative subformula of the form I -o J 
   with I not !-like *)
let rec contains_noc_like_sub = function
  | STensor (_, x, y) | SPlus (_, x, y) | SWith (_, x, y) -> 
      contains_noc_like_sub x || contains_noc_like_sub y
  | SImpl (bl, x, y) -> 
      if not (bl || is_oc_like x) then true
      else
        contains_noc_like_sub x || contains_noc_like_sub y
  | SOfCourse (_, x) -> contains_noc_like_sub x
  | _ -> false 

(* Determine if a formula is almost zero *)
let rec is_almost_zero = function
  | SZero _ -> true
  | STensor (_, x, y) | SWith (_, x, y) -> is_almost_zero x || is_almost_zero y
  | SPlus (_, x, y) -> is_almost_zero x && is_almost_zero y
  | _ -> false 
  
(* Determine if a formula contains a negative subformula of the form I -o Z *)
let rec contains_alm_zero_sub = function
  | STensor (_, x, y) | SPlus (_, x, y) | SWith (_ ,x, y) -> 
      contains_alm_zero_sub x || contains_alm_zero_sub y
  | SImpl (bl, x, y) ->
      if (not bl) && is_almost_zero y then true
      else
        contains_alm_zero_sub x || contains_alm_zero_sub y
  | SOfCourse (_, x) -> contains_alm_zero_sub x 
  | _ -> false 

(* Determine if a formula contains a negative subformula 0 or a positive
   subformula top *)
and contains_pos_top_or_neg_zero = function
  | STensor (_, x, y) | SPlus (_, x, y) | SWith (_, x, y) | SImpl (_, x, y) -> 
      contains_pos_top_or_neg_zero x || contains_pos_top_or_neg_zero y
  | SOfCourse (_, x) -> contains_pos_top_or_neg_zero x
  | STop bl -> bl
  | SZero bl -> not bl 
  | _ -> false 

let possible_counterexample skel = 
  contains_pos_top_or_neg_zero skel && contains_noc_like_sub skel &&
  contains_alm_zero_sub skel

let assign_bl bl = function
  | STensor (_, x, y) -> STensor (bl, x, y)
  | SWith (_, x, y) -> SWith (bl, x, y)
  | SPlus (_, x, y) -> SPlus (bl, x, y)
  | SImpl (_, x, y) -> SImpl (bl, x, y) 
  | SOfCourse (_, x) -> SOfCourse (bl, x)
  | SLeaf (_, i) -> SLeaf (bl, i)
  | STop _ -> STop bl
  | SOne _ -> SOne bl
  | SZero _ -> SZero bl
  | SAtom (_, name) -> SAtom (bl, name)

(* Assign a new skeleton (STop, SOne, SZero, SAtom) to the leaf of index n *)  
let rec assign skel n leaf = match skel with
  | STensor (bl, x, y) -> STensor (bl, assign x n leaf, assign y n leaf)
  | SWith (bl, x, y) -> SWith (bl, assign x n leaf, assign y n leaf)
  | SPlus (bl, x, y) -> SPlus (bl, assign x n leaf, assign y n leaf)
  | SImpl (bl, x, y) -> SImpl (bl, assign x n leaf, assign y n leaf)
  | SOfCourse (bl, x) -> SOfCourse (bl, assign x n leaf)  
  | SLeaf (bl, m) when m = n -> assign_bl bl leaf
  | _ -> skel   

module Set_skel = Set.Make(struct type t = skeleton let compare = compare end)

(* Transform a complete skeletons (with no leaf anonymous) into a formula *)
let rec skel_to_formula = function
  | STensor (_, x, y) -> Tensor (skel_to_formula x, skel_to_formula y)
  | SWith (_, x, y) -> With (skel_to_formula x, skel_to_formula y)
  | SPlus (_, x, y) -> Plus (skel_to_formula x, skel_to_formula y)
  | SImpl (_, x, y) -> Impl (skel_to_formula x, skel_to_formula y)
  | SOfCourse (_, x) -> OfCourse (skel_to_formula x) 
  | STop _ -> Top
  | SOne _ -> One
  | SZero _ -> Zero
  | SAtom (_, i) -> Pos ("X" ^ string_of_int i)
  | SLeaf _ -> assert false  

let generate_formulas skel =
  let n = nb_leaves skel in
  let formulas = ref [] in
  let choices = Set_skel.of_list [STop true; SOne true; SZero true] in
  let rec assign_skel skeleton m choices new_var =
    if m = n then begin
      if possible_counterexample skeleton then begin
        formulas := skel_to_formula skeleton :: !formulas end
      else () end
    else
      Set_skel.iter 
        (fun x -> 
           if x = SAtom (true, new_var) then
             assign_skel (assign skeleton m x) (m + 1) (Set_skel.add x choices)
             (new_var + 1)
           else
             assign_skel (assign skeleton m x) (m + 1) choices new_var)
        (Set_skel.add (SAtom (true, new_var)) choices) in 
  assign_skel skel 0 choices 0;
  !formulas 

(* Hashtbl.find tbl_skel' (n, m) = the list of skeletons of implicative order n
   and containing n operators *)
(* Here we only take additive and multiplicative operators into consideration *)
let tbl_skel' : ((int * int), skeleton list) Hashtbl.t = Hashtbl.create 30  

let add_not_impl_binop x y = 
  let k = nb_leaves x in
  [STensor (true, x, add_index k y); SPlus (true, x, add_index k y); 
   SWith (true, x, add_index k y)]

let add_impl x y = 
  let k = nb_leaves x in [SImpl (true, inv_polarity x, add_index k y)]

let rec generate_skeletons_order n m =
  try Hashtbl.find tbl_skel' (n, m) 
  with Not_found -> match (n, m) with
    | _ when n > m -> [] 
    | 0, 0 -> 
        Hashtbl.add tbl_skel' (0, 0) [SLeaf (true, 0)]; [SLeaf (true, 0)]
    | _ ->
        let tmp = ref [] in
        for i = 0 to m - 1 do 
          tmp := map_product add_not_impl_binop 
                 (generate_skeletons_order n i)
                 (generate_skeletons_order n (m-1-i)) @ !tmp;
        done;
        for i = 0 to m - 1 do
          for j = 0 to n - 1 do begin 
            tmp := map_product add_not_impl_binop 
                   (generate_skeletons_order n i)
                   (generate_skeletons_order j (m-1-i)) @ !tmp;
            tmp := map_product add_not_impl_binop
                   (generate_skeletons_order j (m-1-i))
                   (generate_skeletons_order n i) @ !tmp end
          done;  
        done;
        
        for i = 0 to m - 1 do begin 
          tmp := map_product add_impl 
                 (generate_skeletons_order (n-1) i)
                 (generate_skeletons_order n (m-1-i)) @ !tmp;
          for j = 0 to n - 1 do begin
            tmp := map_product add_impl 
                   (generate_skeletons_order (n-1) i)
                   (generate_skeletons_order j (m-1-i)) @ !tmp;
            if j <> n - 1 then
              tmp := map_product add_impl 
                     (generate_skeletons_order j i)
                     (generate_skeletons_order n (m-1-i)) @ !tmp; end
          done;
          end
        done;
        Hashtbl.add tbl_skel' (n, m) !tmp; 
        !tmp

let rec compare f g = match (f, g) with
  | Tensor (f', One), _ | Tensor (One, f'), _ when compare f' g = 0 -> 0
  | _, Tensor (g', One) | _, Tensor (One, g') when compare f g' = 0 -> 0
  | Par (f', Bottom), _ | Par (Bottom, f'), _ when compare f' g = 0 -> 0
  | _, Par (g', Bottom) | _, Par (Bottom, g') when compare f g' = 0 -> 0 
  | Plus (f', Zero), _  | Plus (Zero, f'), _  when compare f' g = 0 -> 0
  | _, Plus (g', Zero)  | _, Plus (Zero, g')  when compare f g' = 0 -> 0
  | With (f', Top), _   | With (Top, f'), _   when compare f' g = 0 -> 0
  | _, With (g', Top)   | _, With (g', Top)   when compare f g' = 0 -> 0
  | Tensor (f1, f2), Tensor (g1, g2) | With (f1, f2), With (g1, g2) 
  | Par (f1, f2), Par (g1, g2) | Plus (f1, f2), Plus (g1, g2) 
    when (compare f1 g1 = 0 && compare f2 g2 = 0) || 
         (compare f1 g2 = 0 && compare f2 g1 = 0) -> 0 
  | Impl (f1, f2), Impl (g1, g2) when compare f1 g1 = 0 && compare f2 g2 = 0 ->
      0
  | _ -> Pervasives.compare f g

module Set_equiv_formula = 
  Set.Make(struct type t = formula let compare = compare end)

let find_counterexamples_order2 m =
  let ff = Format.std_formatter in
  let skels = generate_skeletons_order 2 m in
  print_int (List.length skels);
  print_string " skeletons have been created";
  print_newline ();
  let l = ref [] in
  List.iter 
    (fun skel -> l := List.filter check_formula (generate_formulas skel) @ !l) skels;
  print_int (List.length !l);
  print_string " possible counterexamples";
  print_newline ();
  let counterexamples = List.filter check_formula !l in
  if counterexamples = [] then 
    Printf.printf "No counterexample found"
  else begin
    print_int (List.length counterexamples);
    Printf.printf " counterexamples found : ";
    print_newline ();
    List.iter (fun x -> print_formula ff x; print_newline ()) counterexamples
  end

let find_counterexamples n m =
  let filename = "counterexamples/" ^ string_of_int n ^ "_" ^ string_of_int m in
  let oc = open_out filename in
  let ff = Format.formatter_of_out_channel oc in 
  generate_skeletons n m;
  let skels = 
    List.filter (check_implicative_order 2) (Hashtbl.find tbl_skel (n,m)) in
  Format.fprintf ff "%d" (List.length skels);
  print_str_line ff " skeletons have been created";
  let l =  
    List.fold_left 
      (fun res skel -> generate_formulas skel @ res) [] skels in 

  Format.fprintf ff "%d" (List.length l);
  print_str_line ff " possible counterexamples";
  let counterexamples = List.filter check_formula2 l in
  if counterexamples = [] then 
    print_str_line ff "No counterexample found"
  else begin 
    Format.fprintf ff "%d" (List.length counterexamples);
    print_str_line ff " counterexamples found : ";
    List.iter (fun x -> print_formula ff x; Format.fprintf ff "\n") counterexamples;
    let equiv_set = 
      List.fold_left 
        (fun s f -> Set_equiv_formula.add f s)
          Set_equiv_formula.empty counterexamples in
    Format.fprintf ff "%d" (Set_equiv_formula.cardinal equiv_set);
    print_str_line ff " equivalence classes : ";
    Set_equiv_formula.iter 
      (fun x -> print_formula ff x; Format.fprintf ff "\n")
      equiv_set;
    close_out oc
  end

let find n = 
  create n;
  let i = ref 0 in 
  let res = ref None in
  while !i < n do
    let res_i = 
      List.fold_left 
        (fun res x -> 
          if res = None then if check_formula x then Some [x] else None
          else
            if check_formula2 x then Some (x :: get_op res)
            else res) None tbl.(!i) in
    res := res_i; 
    incr i;
  done;
  if !res = None then
    Printf.printf "No counterexample found"
  else begin 
    Printf.printf "Counterexamples found : ";
    print_newline ();
    let ff = Format.std_formatter in
    List.iter (fun x -> print_formula ff x; print_newline ()) (get_op !res) end
