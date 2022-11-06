open Lexer

type expr =
  | Num of float
  | Sum of expr * expr
  | Sub of expr * expr
  | Mul of expr * expr
  | Div of expr * expr

exception ParseError of string

let parser_error (err : string) : string = "Syntax error: " ^ err
let tokens : token list ref = ref []

let tok_to_str (tok : token) : string =
  match tok with
  | Number value -> string_of_float value
  | Plus ch -> Char.escaped ch
  | Minus ch -> Char.escaped ch
  | Star ch -> Char.escaped ch
  | Slash ch -> Char.escaped ch
  | L_Paren ch -> Char.escaped ch
  | R_Paren ch -> Char.escaped ch
  | EOL -> ""

let peek () : token =
  match !tokens with
  | h :: t -> h
  | _ -> raise (ParseError (parser_error "mismatched parentheses"))

let advance () : unit =
  match !tokens with
  | h :: t -> tokens := t
  | _ -> raise (ParseError (parser_error ""))

let rec parse_expr () : expr =
  (* E -> T *)
  let e = parse_term () in

  let rec loop (e : expr) : expr =
    (* E -> T + T *)
    (* E -> T - T *)
    match peek () with
    | Plus _ ->
        advance ();
        let right = parse_term () in
        loop (Sum (e, right))
    | Minus _ ->
        advance ();
        let right = parse_term () in
        loop (Sub (e, right))
    | _ -> e
  in
  loop e

and parse_term () : expr =
  (* T -> F *)
  let e = parse_fact () in

  let rec loop (e : expr) : expr =
    (* T -> F * F *)
    (* T -> F / F  *)
    match peek () with
    | Star _ ->
        advance ();
        let right = parse_fact () in
        loop (Mul (e, right))
    | Slash _ ->
        advance ();
        let right = parse_fact () in
        loop (Div (e, right))
    | _ -> e
  in
  loop e

and parse_fact () : expr =
  (* F -> n *)
  (* F -> ( E ) *)
  match peek () with
  | Number value ->
      advance ();
      Num value
  | L_Paren _ ->
      advance ();
      let e = parse_expr () in
      advance ();
      e
  | _ -> raise (ParseError (peek () |> tok_to_str |> parser_error))

(*
Grammar:
  E -> T | T + T | T - T
  T -> F | F * F | F / F
  F -> n | ( E )
*)
let parse (t : token list) : expr =
  tokens := t;
  parse_expr ()
