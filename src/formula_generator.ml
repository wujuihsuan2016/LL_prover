open Formula
open Printer
open Format

(* Generator of provable sequents using purely positive affine formula
   (rejecting !, -o and &), introduced by O. Laurent in "Around Classical and
   Intuitionistic Linear Logics" *)

let x = Par (Pos "X", Neg "X")

let l = [One; Zero; Top; x] 

let rec create_pairs l acc = match l with
  | [] -> acc
  | hd :: tl -> 
      let acc' = 
        List.fold_left 
          (fun l x -> 
            [(x, hd, true); (x, hd, false); (hd, x, true); (hd, x, false)] @ l)
          acc l
      in create_pairs tl acc' 

let q = Queue.create ()

let () = List.iter (fun x -> Queue.add x q) (create_pairs l [])

let purely_positive_affine = ref [One; Zero; Top; x] 

let card = ref 4

let create_sequents n = 
  while !card < n do begin
    incr card;
    let (f1, f2, bl) = Queue.take q in
    match bl with
      | true -> 
          let new_f = Tensor (f1, f2) in
          purely_positive_affine := new_f :: !purely_positive_affine; 
          List.iter 
            (fun x -> 
              Queue.add (x, new_f, true) q;
              Queue.add (x, new_f, false) q;
              Queue.add (new_f, x, true) q;
              Queue.add (new_f, x, false) q) (List.rev !purely_positive_affine)
      | false ->
          let new_f = Plus (f1, f2) in
          purely_positive_affine := new_f :: !purely_positive_affine;
          List.iter 
            (fun x ->
              Queue.add (x, new_f, true) q;
              Queue.add (x, new_f, false) q;
              Queue.add (new_f, x, true) q;
              Queue.add (new_f, x, false) q) (List.rev !purely_positive_affine) 
     end
  done

let r = Pos "Y" 

(* The translation of a formula of LL is a formula of ILL *)

let rec translation = function
  | Pos x -> Impl (Pos x, r)
  | Neg x -> Pos x
  | One -> Impl (One, r) 
  | Zero -> Impl (Zero, r)
  | Bottom -> One
  | Top -> Zero
  | Tensor (f, g) -> 
      Impl (Tensor (Impl (translation f, r), Impl (translation g, r)), r)
  | Plus (f, g) ->
      Impl (Plus (Impl (translation f, r), Impl (translation g, r)), r)
  | Par (f, g) -> Tensor (translation f, translation g)
  | With (f, g) -> Plus (translation f, translation g)
  | OfCourse f -> Impl (OfCourse (Impl (translation f, r)), r)
  | Whynot f -> OfCourse (Impl (Impl (translation f, r), r))



let main () = 
  create_sequents (int_of_string Sys.argv.(1));
  let i = ref 1 in 
  let print_seq f =
    let file = "sequents/" ^ (string_of_int !i) in 
    let oc = open_out file in
    let fmt = formatter_of_out_channel oc in
    let sequent = ([f], [Impl (translation f, r)]) in
    print_sequent_2 fmt sequent;
    flush oc;
    incr i;
    close_out oc 
  in 
  List.iter print_seq (List.rev !purely_positive_affine)

let () = main ()    
