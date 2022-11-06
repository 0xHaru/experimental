type token =
  | Number of float
  | Plus of char
  | Minus of char
  | Star of char
  | Slash of char
  | L_Paren of char
  | R_Paren of char
  | EOL

exception LexError of string

let lexer_error (ch : char) (err : string) : string =
  "Lexical error: " ^ err ^ " '" ^ Char.escaped ch ^ "'"

(** Convert a string into a list of chars *)
let explode (str : string) : char list =
  let rec expl i lst =
    if i < 0 then
      lst
    else
      expl (i - 1) (str.[i] :: lst)
  in
  expl (String.length str - 1) []

(** Convert a list of chars into a string *)
let implode lst =
  let rec impl lst str =
    match lst with
    | [] -> str
    | h :: t -> impl t (str ^ String.make 1 h)
  in
  impl lst ""

let is_digit (ch : char) : bool =
  match ch with
  | '0' .. '9' -> true
  | _ -> false

let consume_number (chars : char list) : token * char list =
  let rec consume (c : char list) (acc : char list) : token * char list =
    match c with
    | ch :: t when is_digit ch || ch = '.' -> consume t (ch :: acc)
    | _ ->
        let number = acc |> List.rev |> implode |> Float.of_string in
        (Number number, c)
  in
  consume chars []

let rec tokenize2 (chars : char list) (tokens : token list) : token list =
  match chars with
  | [] -> tokens
  | ch :: t -> (
      match ch with
      | '+' -> tokenize2 t (Plus '+' :: tokens)
      | '-' -> tokenize2 t (Minus '-' :: tokens)
      | '*' -> tokenize2 t (Star '*' :: tokens)
      | '/' -> tokenize2 t (Slash '/' :: tokens)
      | '(' -> tokenize2 t (L_Paren '(' :: tokens)
      | ')' -> tokenize2 t (R_Paren ')' :: tokens)
      (* Ignore whitespace *)
      | ' ' -> tokenize2 t tokens
      | '\t' -> tokenize2 t tokens
      | '\n' -> tokenize2 t tokens
      | _ -> (
          if not (is_digit ch) then
            raise (LexError (lexer_error ch "unexpected character"))
          else
            match consume_number chars with
            | token, t -> tokenize2 t (token :: tokens)
            | exception Failure str ->
                raise (LexError (lexer_error ch "malformed number"))))

let tokenize (source : string) : token list =
  EOL :: tokenize2 (explode source) [] |> List.rev
