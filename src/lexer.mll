{
  open Parser
  open Lexing

  exception Lexing_error of string 
}

let letter = ['a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let space = '\t' | ' ' | '\n'
let id = letter (letter | digit | '_')*
let newline = '\n' | '\r' '\n'

rule token = parse 
  | newline { new_line lexbuf; token lexbuf }
  | space+  { token lexbuf }
  | "(*"    { nested_comment lexbuf; token lexbuf }
  | ","     { COMMA }
  | "|-"    { IMPL }
  | "o-o"   { DIMPL }
  | "-o"    { LIMPL }
  | "("     { LPAREN }
  | ")"     { RPAREN }
  | "^"     { NOT }
  | "?"     { WHYNOT }
  | "!"     { OFCOUR }
  | "bot"   { BOT }
  | "top"   { TOP }
  | "0"     { ZERO }
  | "1"     { ONE }
  | "*"     { TENSOR }
  | "|"     { PAR }
  | "&"     { WITH }
  | "+"     { PLUS }
  | id as s { STR s }
  | eof     { EOF }
  | _ as c  { raise (Lexing_error ("Illegal character: " ^ String.make 1 c)) }

and nested_comment = parse 
  | newline { new_line lexbuf; nested_comment lexbuf }
  | "*)"    { () }
  | "(*"    { nested_comment lexbuf; nested_comment lexbuf }
  | _       { nested_comment lexbuf }
  | eof     { raise (Lexing_error "Comment not terminated") }

