open Lexing 
open Formula
open Fctns

let in_ill = ref false
let use_inverse_method = ref false
let coq_export = ref false
let latex_export = ref false
let foc_latex_export = ref false

let bound = ref 3
let dest_res_file = ref false


let options = 
  ["-ill", Arg.Set in_ill, "Choose ILL as the logical system"; 
   "-inv", Arg.Set use_inverse_method, "use inverse method";
   "-coq", Arg.Set coq_export, "output a proof certificate";
   "-latex", Arg.Set latex_export, 
   "output the latex code of the corresponding proof tree";
   "-flatex", Arg.Set foc_latex_export, 
   "output the latex code of the corresponding focused proof tree";
   "-res_to_file", Arg.Set dest_res_file, "store the result in the file *.res";
   "-bound", Arg.Set_int bound, "A (pseudo-)bound for the contraction rule"]

let usage_msg = "Usage: prover.byte [option] filename"

let file = ref ""

let locate pos =
  let l = pos.pos_lnum in
  let c = pos.pos_cnum - pos.pos_bol + 1 in
  Printf.eprintf "File \"%s\", line %d, characters %d-%d\n" !file l (c-1) c

let set_file f f' = f := f' 

let main () =
  Arg.parse options (set_file file) usage_msg; 
  let f = open_in !file in
  let buf = Lexing.from_channel f in
  try 
    let (formula_list1, formula_list2) = Parser.file Lexer.token buf in 
    match not !in_ill with
      | true -> 
          let l = 
            List.map neg_formula formula_list1 @ List.map rewrite formula_list2 
          in
          let sequent = Async (Set_formula.empty, [], l) in
          let oc = 
            if !dest_res_file then open_out (!file ^ "_ll.res") 
            else stdout in
          let ff = Format.formatter_of_out_channel oc in
          let res = 
            if !use_inverse_method then Foc_ll_inv.prove_sequent sequent !bound 
            else Foc.prove_sequent sequent !bound in
          begin match res with
            | None, _, t -> 
                Format.fprintf ff "File \"%s\": No proof found. Execution time: %fms.\n@?" 
                !file (t *. 1000.);
                close_out oc
            | Some bl, opt, t -> 
                Format.fprintf ff "File \"%s\": %s. Execution time: %fms.\n@?"
                !file
                (if bl then "Provable" else "Not provable")
                (t *. 1000.);
                close_out oc;
                if bl then begin try
                  let proof = get_op opt in
                  (if !latex_export then 
                    Export_latex.output_proof_ll proof !file);
                  (if !foc_latex_export then 
                    Export_latex.output_proof_llf proof !file);
                  (if !coq_export then 
                    Export_coq.output_proof_ll l proof !file)  
                  with _ -> ()
                end
          end
      | false ->
          let omega = formula_list1 in
          if formula_list2 = [] || List.tl formula_list2 <> [] then begin
            Format.eprintf "Unvalid sequent";
            exit 1
          end;
          let [@warning "-8"] [formula] = formula_list2 in 
          let bwd_sequent = Active (Set_formula.empty, [], omega, formula) in
          match !use_inverse_method with
            | true ->
                let oc = 
                  if !dest_res_file then open_out (!file ^ "_ill_inv.res")
                  else stdout in
                let ff = Format.formatter_of_out_channel oc in
                begin match Foc_inv.prove_sequent bwd_sequent !bound with
                  | true, t -> 
                      Format.fprintf ff "File \"%s\": Provable. Execution time: %fms.\n@?"
                      !file
                      (t *. 1000.);
                      close_out oc
                  | false, t -> 
                      Format.fprintf ff "File \"%s\": No proof found. Execution time: %fms.\n@?"
                      !file
                      (t *. 1000.);
                      close_out oc
                end
            | false ->
                let oc = 
                  if !dest_res_file then open_out (!file ^ "_ill.res")
                  else stdout in
                let ff = Format.formatter_of_out_channel oc in
                match Foc_ill.prove_sequent bwd_sequent !bound with
                  | None, _, t ->
                      Format.fprintf ff 
                      "File \"%s\": No proof found. Execution time: %fms.\n@?"
                      !file
                      (t *. 1000.);
                      close_out oc
                  | Some bl, opt, t ->
                      Format.fprintf ff 
                      "File \"%s\": %s. Execution time: %fms.\n@?"
                      !file
                      (if bl then "Provable" else "Not provable")
                      (t *. 1000.);
                      close_out oc;
                      if bl then begin
                        let proof = get_op opt in
                        (if !latex_export then 
                          Export_latex.output_proof_ill proof !file);
                        (if !foc_latex_export then
                          Export_latex.output_proof_illf proof !file);
                        (if !coq_export then
                          Export_coq.output_proof_ill bwd_sequent proof !file)
                      end
  with
    | Lexer.Lexing_error msg ->
        locate (Lexing.lexeme_start_p buf);
        Format.eprintf "%s@?" msg;
        exit 1
    | Parser.Error ->
        locate (Lexing.lexeme_start_p buf);
        Format.eprintf "Syntax error@?";
        exit 1

let () = main ()
