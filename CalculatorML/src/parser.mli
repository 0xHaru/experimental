type expr =
  | Num of float
  | Sum of expr * expr
  | Sub of expr * expr
  | Mul of expr * expr
  | Div of expr * expr

exception ParseError of string

val parse : Lexer.token list -> expr
