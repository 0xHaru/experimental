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

val tokenize : string -> token list
