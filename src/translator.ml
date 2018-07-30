(* Translate formulas from Girard's notation into Troelstra's notation *)

open Formula
open Format
open Fctns

let var_tbl = Hashtbl.create 26
let ascii = ref 97

let rec fill_tbl = function
  | Pos x | Neg x -> 
      if not (Hashtbl.mem var_tbl x) then begin
        Hashtbl.add var_tbl x (String.make 1 (Char.chr !ascii));
        incr ascii end
  | One | Zero | Top | Bottom -> ()
  | OfCourse f | Whynot f -> fill_tbl f
  | Tensor (f, g) | Plus (f, g) | With (f, g) | Par (f, g) | Impl (f, g) ->
      fill_tbl f; fill_tbl g

let rec print_unop ff fmt f =
  if not (is_binop f) then
    fprintf ff fmt print_formula f
  else
    fprintf ff fmt print_formula_with_paren f

and print_binop ff fmt f g = 
  if not (is_binop f) then 
    if not (is_binop g) then
      fprintf ff fmt print_formula f print_formula g
    else
      fprintf ff fmt print_formula f print_formula_with_paren g
  else
    if not (is_binop g) then
      fprintf ff fmt print_formula_with_paren f print_formula g
    else
      fprintf ff fmt print_formula_with_paren f print_formula_with_paren g

and print_formula ff = function
  | Pos s -> Printer.print_str ff (Hashtbl.find var_tbl s)
  | Neg s -> fprintf ff "~%s@?" (Hashtbl.find var_tbl s) 
  | One -> fprintf ff "1@?"
  | Zero -> fprintf ff "bot@?"
  | Top -> fprintf ff "top@?"
  | Bottom -> fprintf ff "0@?"
  | OfCourse f -> print_unop ff "!%a@?" f
  | Whynot f -> print_unop ff "?%a@?" f 
  | Tensor (f, g) -> print_binop ff "%a * %a@?" f g
  | Plus (f, g) -> print_binop ff "%a \\/ %a@?" f g 
  | With (f, g) -> print_binop ff "%a /\\ %a@?" f g
  | Par (f, g) -> print_binop ff "%a + %a@?" f g
  | Impl (f, g) -> print_binop ff "%a -> %a@?" f g

and print_formula_with_paren ff formula = 
  fprintf ff "(%a)" print_formula formula

let print_formula_list ff l = 
  if l = [] then fprintf ff "[]@?"
  else
    fprintf ff "%a" (pp_print_list ~pp_sep:Printer.print_sep print_formula) l

let print_sequent ff (left, right) =
  fprintf ff "@[%a --> %a]@"
  print_formula_list left
  print_formula_list right

let main () = 
  let f = open_in Sys.argv.(1) in
  let buf = Lexing.from_channel f in
  let (left, right) = Parser.file Lexer.token buf in 
  List.iter fill_tbl left;
  List.iter fill_tbl right;
  let oc = open_out (Sys.argv.(1) ^ "_") in
  let ff = formatter_of_out_channel oc in
  print_sequent ff (left, right);
  close_out oc

let () = main ()
