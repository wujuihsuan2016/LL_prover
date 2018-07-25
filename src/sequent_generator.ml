(* A simple generator of provable sequents of LL *)

open Formula
open Printer
open Format

let rec mult_par m f = match m with
  | 1 -> f
  | _ -> Par (f, mult_par (m-1) f)

let rec gcd m n =
  if m < n then gcd n m
  else
    if m mod n = 0 then n
    else gcd n (m mod n)  

let copy n f = 
  let rec copy_aux n f acc = match n with
    | 0 -> acc
    | _ -> copy_aux (n-1) f (f :: acc)
  in copy_aux n f []

let lcm m n = (m * n) / (gcd m n)

let create_sequent m n = 
  let ma = Whynot (mult_par m (Pos "A")) in 
  let nb = Whynot (mult_par n (Pos "B")) in
  let c = 
    copy ((*lcm m n*) 1) (Whynot (Tensor (Neg "A", (Tensor (Neg "B", Neg "C"))))) in
  ([], [ma; nb; Whynot (Tensor ((Pos "C"), Bottom)); (Pos "C")] @ c)

let main () =
  let i = ref 1 in
  for m = 1 to (int_of_string Sys.argv.(1)) do
    for n = 1 to (int_of_string Sys.argv.(2)) do
      let sequent = create_sequent m n in
      let file = 
        "sequent_lcm/" ^ (string_of_int !i) in
      let oc = open_out file in
      let ff = formatter_of_out_channel oc in
      print_sequent_2 ff sequent;
      incr i;
      close_out oc;
    done;
  done

let () = main ()
