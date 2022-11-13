module type StackSig = sig
  type 'a t

  exception Empty

  val empty : unit -> 'a t
  val push : 'a -> 'a t -> unit
  val pop : 'a t -> 'a
  val peek : 'a t -> 'a
end

module MutableStack : StackSig = struct
  type 'a t = { mutable stack : 'a list }

  exception Empty

  let empty () = { stack = [] }
  let push x s = s.stack <- x :: s.stack

  let pop s =
    match s.stack with
    | [] -> raise Empty
    | h :: t ->
        s.stack <- t;
        h

  let peek s =
    match s.stack with
    | [] -> raise Empty
    | h :: t -> h
end

module type PolishCalcSig = sig
  type expr

  val expr_of_string : string -> expr
  val string_of_expr : expr -> string
  val eval : expr -> int
end

module PolishCalcFunct (Stack : StackSig) : PolishCalcSig = struct
  type expr =
    | Num of int
    | Sum of expr * expr
    | Sub of expr * expr
    | Mul of expr * expr
    | Div of expr * expr
    | Pow of expr * expr

  let expr_of_string str =
    let stack = Stack.empty () in
    let get_expr ch =
      match ch with
      | "+" -> Sum (Stack.pop stack, Stack.pop stack)
      | "-" -> Sub (Stack.pop stack, Stack.pop stack)
      | "*" -> Mul (Stack.pop stack, Stack.pop stack)
      | "/" -> Div (Stack.pop stack, Stack.pop stack)
      | "^" -> Pow (Stack.pop stack, Stack.pop stack)
      | n -> Num (int_of_string n)
    in
    let rec loop lst =
      match lst with
      | [] -> Stack.peek stack
      | h :: t ->
          Stack.push (get_expr h) stack;
          loop t
    in
    loop (Str.split (Str.regexp " +") str)

  let rec string_of_expr e =
    match e with
    | Sum (e1, e2) -> "(" ^ string_of_expr e1 ^ " + " ^ string_of_expr e2 ^ ")"
    | Sub (e1, e2) -> "(" ^ string_of_expr e1 ^ " - " ^ string_of_expr e2 ^ ")"
    | Mul (e1, e2) -> "(" ^ string_of_expr e1 ^ " * " ^ string_of_expr e2 ^ ")"
    | Div (e1, e2) -> "(" ^ string_of_expr e1 ^ " / " ^ string_of_expr e2 ^ ")"
    | Pow (e1, e2) -> "(" ^ string_of_expr e1 ^ " ^ " ^ string_of_expr e2 ^ ")"
    | Num n -> string_of_int n

  let rec eval e =
    match e with
    | Sum (e1, e2) -> eval e1 + eval e2
    | Sub (e1, e2) -> eval e1 - eval e2
    | Mul (e1, e2) -> eval e1 * eval e2
    | Div (e1, e2) -> eval e1 / eval e2
    | Pow (e1, e2) -> int_of_float (float_of_int (eval e1) ** float_of_int (eval e2))
    | Num n -> n
end

module PolishCalculator = PolishCalcFunct (MutableStack)

let main () =
  let e = PolishCalculator.expr_of_string "3 4 + 5 *" in
  let str = PolishCalculator.string_of_expr e in
  let result = PolishCalculator.eval e in
  Printf.printf "expr: 3 4 + 5 *\n";
  Printf.printf "string_of_expr: %s\n" str;
  Printf.printf "result: %d\n" result
;;

main ()
