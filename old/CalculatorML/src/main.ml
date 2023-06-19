open Lexer
open Parser
open Printf

let rec eval (e : expr) : float =
  match e with
  | Num n -> n
  | Sum (e1, e2) -> eval e1 +. eval e2
  | Sub (e1, e2) -> eval e1 -. eval e2
  | Mul (e1, e2) -> eval e1 *. eval e2
  | Div (e1, e2) -> eval e1 /. eval e2

let rec repl () : unit =
  (try
     print_string "> ";
     let input = read_line () in

     let tokens = tokenize input in
     let expr = parse tokens in
     printf "%f\n" (eval expr)
   with
  | LexError err -> print_string (err ^ "\n")
  | ParseError err -> print_string (err ^ "\n")
  | End_of_file ->
      print_string "\n";
      exit 0);
  repl ()
;;

print_string "Press CTRL + D to quit\n";
repl ()
