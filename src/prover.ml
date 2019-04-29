open Lexing 
open Formula
open Fctns

let in_ill = ref false
let use_inverse_method = ref false
let coq_export = ref false
let latex_export = ref false
let foc_latex_export = ref false
let bound = ref 3
let file = ref ""
let ofile = ref ""
let to_terminal = ref false
let from_terminal = ref "" 
let only_latex = ref false
let lltp_format = ref false
let ptree_export = ref false

let options = 
  ["-ill", Arg.Set in_ill, " Choose ILL as the logical system"; 
   "-inv", Arg.Set use_inverse_method, " Use the inverse method";
   "-c", Arg.Set coq_export, " Output a proof certificate in Coq";
   "-l", Arg.Set latex_export, 
   " Output the latex code the corresponding proof tree";
   "-lf", Arg.Set foc_latex_export, 
   " Output the latex code of the corresponding focused proof tree";
   "-ptree", Arg.Set ptree_export,
   " Output the proof tree in the internal syntax";
   "-bound", Arg.Set_int bound, "<number>  A (pseudo-)bound for the contraction rule";
   "-o", Arg.Set_string ofile, "<foldername>  Set the name of output folder";
   "-t", Arg.Set to_terminal, " Print the result in the terminal";
   "-s", Arg.Set_string from_terminal, " The input is the standard input";
   "-lltp", Arg.Set lltp_format, " Input in LLTP format";
   "-ol", Arg.Set only_latex, " Only output the latex code of the sequent"]

let usage_msg = "Usage: prover.byte [option] filename"

let locate pos =
  let l = pos.pos_lnum in
  let c = pos.pos_cnum - pos.pos_bol + 1 in
  Printf.eprintf "File \"%s\", line %d, characters %d-%d\n" !file l (c-1) c

let set_file f f' = f := f' 

let main () =
  Arg.parse options (set_file file) usage_msg; 
  let buf =
    if !from_terminal = "" then Lexing.from_channel (open_in !file)
    else Lexing.from_string !from_terminal in
  try 
    let (formula_list1, formula_list2) = 
      if !lltp_format then Parser.lltp_file Lexer.lltp_token buf
      else Parser.file Lexer.token buf in 
    match not !in_ill with
      | true -> 
          let l = 
            List.map neg_formula formula_list1 @ List.map rewrite formula_list2 
          in
          let sequent = Async (Set_formula.empty, [], l) in
          let folder = "result/ll/" ^ !ofile in
          let oc = 
            if !ofile = "" || !to_terminal then stdout
            else open_out (folder ^ "/result.txt") in
          let ff = Format.formatter_of_out_channel oc in
          (if !only_latex then begin
            let oc' = 
              if !ofile = "" || !to_terminal then stdout
              else open_out (folder ^ "/sequent.tex") in
            let ff' = Format.formatter_of_out_channel oc' in
            Export_latex.print_latex_sequent ff' (formula_list1, formula_list2);
            exit 0 end);
          let res = 
            if !use_inverse_method then Foc_ll_inv.prove_sequent sequent !bound 
            else Foc_ll_bwd.prove_sequent sequent !bound in
          begin match res with
            | None, _, t -> 
                Format.fprintf ff "%a\n-\n%f\n@?" 
                Printer.print_sequent_2 (formula_list1, formula_list2)
                (t *. 1000.);
                close_out oc
            | Some bl, opt, t -> 
                Format.fprintf ff "%a\n%s\n%f\n@?"
                Printer.print_sequent_2 (formula_list1, formula_list2)
                (if bl then "P" else "N") (t *. 1000.);
                close_out oc;
                if bl then begin try
                  let proof = get_op opt in
                  (if !latex_export then 
                    Export_latex.output_proof_ll proof (folder ^ "/proof.tex"));
                  (if !foc_latex_export then 
                    Export_latex.output_proof_llf proof 
                    (folder ^ "/proof_focused.tex"));
                  (if !coq_export then 
                    Export_coq.output_proof_ll l proof (folder ^ "/proof.v"));
                  (if !ptree_export then
                    Printer.output_proof_ll proof (folder ^ "/proof.apll"))
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
          let folder = "result/ill/" ^ !ofile in
          let oc = 
            if !ofile = "" || !to_terminal then stdout
            else open_out (folder ^ "/result.txt") in
          let ff = Format.formatter_of_out_channel oc in
          (if !only_latex then begin
            let oc' = 
              if !ofile = "" || !to_terminal then stdout
              else open_out (folder ^ "/sequent.tex") in
            let ff' = Format.formatter_of_out_channel oc' in
            Export_latex.print_ill_latex_sequent ff' bwd_sequent;
            exit 0 end);
          match !use_inverse_method with
            | true ->
                begin match Foc_ill_inv.prove_sequent bwd_sequent !bound with
                  | true, t -> 
                      Format.fprintf ff "%a\nP\n%f\n@?" 
                      Printer.print_sequent_2 (formula_list1, formula_list2)
                      (t *. 1000.);
                      close_out oc
                  | false, t -> 
                      Format.fprintf ff "%a\n-\n%f\n@?" 
                      Printer.print_sequent_2 (formula_list1, formula_list2)
                      (t *. 1000.);
                      close_out oc
                end
            | false ->
                match Foc_ill_bwd.prove_sequent bwd_sequent !bound with
                  | None, _, t ->
                      Format.fprintf ff "%a\n-\n%f\n@?" 
                      Printer.print_sequent_2 (formula_list1, formula_list2)
                      (t *. 1000.);
                      close_out oc
                  | Some bl, opt, t ->
                      Format.fprintf ff "%a\n%s\n%f\n@?" 
                      Printer.print_sequent_2 (formula_list1, formula_list2)
                      (if bl then "P" else "N")
                      (t *. 1000.);
                      close_out oc;
                      if bl then begin
                        let proof = get_op opt in
                        (if !latex_export then 
                          Export_latex.output_proof_ill proof 
                          (folder ^ "/proof.tex"));
                        (if !foc_latex_export then
                          Export_latex.output_proof_illf proof 
                          (folder ^ "/proof_focused.tex"));
                        (if !coq_export then
                          Export_coq.output_proof_ill bwd_sequent proof 
                          (folder ^ "/proof.v"));
                        (if !ptree_export then
                          Printer.output_proof_ill proof
                          (folder ^ "/proof.apll"))
                      end
  with
    | Lexer.Lexing_error msg ->
        let folder = (if !in_ill then "result/ill/" else "result/ll/") ^ !ofile in
        let oc = 
          if !ofile = "" || !to_terminal then stdout
          else open_out (folder ^ "/result.txt") in
        output_string oc "error";
        close_out oc;
        locate (Lexing.lexeme_start_p buf);
        Format.eprintf "%s@?" msg;
        exit 1
    | Parser.Error ->
        let folder = (if !in_ill then "result/ill/" else "result/ll/") ^ !ofile in
        let oc = 
          if !ofile = "" || !to_terminal then stdout
          else open_out (folder ^ "/result.txt") in
        output_string oc "error";
        close_out oc;
        locate (Lexing.lexeme_start_p buf);
        Format.eprintf "Syntax error@?";
        exit 1

let () = main ()
