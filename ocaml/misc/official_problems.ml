(* https://ocaml.org/problems *)

(*
1. Tail of a list
    Write a function last : 'a list -> 'a option that returns the last element of a list
*)

let rec last list =
  match list with
  | [] -> None
  | [ x ] -> Some x
  | _ :: t -> last t;;

(*
last ["a" ; "b" ; "c" ; "d"];; -> Some "d"
last [];; -> 'a option = None
*)

(* ---------------------------------------------------------------------------------------------- *)

(*
2. Last two elements of a list
    Find the last but one (last and penultimate) elements of a list
*)

let rec last_two list =
  match list with
  | [] | [ _ ] -> None
  | [ x ; y ] -> Some (x, y)
  | _ :: t -> last_two t;;

(*
last_two ["a"; "b"; "c"; "d"];; -> Some ("c", "d")
last_two ["a"];; -> None
*)

(* ---------------------------------------------------------------------------------------------- *)

(*
3. N'th element of a list
    Find the N'th element of a list
*)

let rec nth list n =
  match list with
  | [] -> None
  | h :: t -> if n = 0 then Some h else nth t (n - 1);;

(*
nth ["a"; "b"; "c"; "d"; "e"] 2;; -> Some "c"
nth ["a"] 2;; -> None
*)

(* ---------------------------------------------------------------------------------------------- *)

(*
4. Length of a list
    Find the number of elements of a list
*)

let rec length list =
  match list with
  | [] -> 0
  | _ :: t -> 1 + length t;;

(* Tail recursive version *)
let length_tr list =
  (* Auxiliary function *)
  let rec aux l n =
    match l with
    | [] -> n
    | _ :: t -> aux t (n + 1)
  in
  aux list 0;;

(*
length ["a"; "b"; "c"];; -> 3
length [];; -> 0
*)

(* ---------------------------------------------------------------------------------------------- *)

(*
5. Reverse a list
*)

let rev list =
  let rec aux l1 l2 =
    match l1 with
    | [] -> l2
    | h :: t -> aux t (h :: l2)
  in
  aux list [];;

(*
rev ["a"; "b"; "c"];;
*)

(* ---------------------------------------------------------------------------------------------- *)

(*
6. Palindrome
    Find out whether a list is a palindrome
*)

let is_palindrome list =
  list = rev list;;

(*
is_palindrome ["x"; "a"; "m"; "a"; "x"];; -> true
is_palindrome ["a"; "b"];; -> false
*)

(* ---------------------------------------------------------------------------------------------- *)

(*
7. Flatten a list
    Flatten a nested list structure
*)

type 'a node =
  | One of 'a
  | Many of 'a node list;;

let flatten lst =
  let rec aux lst acc =
    match lst with
    | [] -> acc
    | One h :: t -> aux t (h :: acc)
    | Many h :: t -> aux t (aux h acc)
  in
  List.rev (aux lst []);;

(*
flatten [One "a"; Many [One "b"; Many [One "c" ;One "d"]; One "e"]];;
-> ["a"; "b"; "c"; "d"; "e"]
*)

(* ---------------------------------------------------------------------------------------------- *)

(*
8. Eliminate duplicates
    Eliminate consecutive duplicates of list elements
*)

let rec compress lst =
    match lst with
    | [] -> []
    | [ a ] -> [ a ]
    | a :: (b :: _ as t) -> if a = b then compress t else a :: compress t;;

(*
compress ["a"; "a"; "a"; "a"; "b"; "c"; "c"; "a"; "a"; "d"; "e"; "e"; "e"; "e"];;
-> ["a"; "b"; "c"; "a"; "d"; "e"]
*)

(* ---------------------------------------------------------------------------------------------- *)

(*
9. Pack consecutive duplicates
    Pack consecutive duplicates of list elements into sublists
*)

let pack lst =
  let rec aux lst current acc =
    match lst with
    | [] -> []  (* Can only be reached if original list is empty *)
    | [ x ] -> (x :: current) :: acc
    | a :: (b :: _ as t) ->
       if a = b then
        aux t (a :: current) acc
       else
        aux  t [] ((a :: current) :: acc)
  in
  List.rev (aux lst [] []);;

(*
pack ["a"; "a"; "a"; "a"; "b"; "c"; "c"; "a"; "a"; "d"; "d"; "e"; "e"; "e"; "e"];;
-> [["a"; "a"; "a"; "a"]; ["b"]; ["c"; "c"]; ["a"; "a"]; ["d"; "d"]; ["e"; "e"; "e"; "e"]]
*)

(* ---------------------------------------------------------------------------------------------- *)

(*
10. Run-length encoding
*)

let encode lst =
  let rec aux lst count acc =
    match lst with
    | [] -> []  (* Can only be reached if original list is empty *)
    | [ a ] -> (count + 1, a) :: acc
    | a :: (b :: _ as t) ->
      if a = b then
        aux t (count + 1) acc
      else
        aux t 0 ((count + 1, a) :: acc)
  in
  List.rev (aux lst 0 []);;

(*
encode ["a"; "a"; "a"; "a"; "b"; "c"; "c"; "a"; "a"; "d"; "e"; "e"; "e"; "e"];;
-> [(4, "a"); (1, "b"); (2, "c"); (2, "a"); (1, "d"); (4, "e")]
*)

(* ---------------------------------------------------------------------------------------------- *)

(*
11. Modified run-length encoding
     Modify the result of the previous problem in such a way that if an element has no duplicates it is simply copied into the result list. Only elements with duplicates are transferred as (N E) lists
*)

type 'a rle =
  | One of 'a
  | Many of int * 'a;;

let encode lst =
  let make_tuple count elem = if count = 1 then One elem else Many(count, elem) in
  let rec aux lst count acc =
    match lst with
    | [] -> []
    | [ a ] -> make_tuple (count + 1) a :: acc
    | a :: (b :: _ as t) ->
      if a = b then
        aux t (count + 1) acc
      else
        aux t 0 (make_tuple (count + 1) a :: acc)
  in
  List.rev (aux lst 0 []);;

(*
encode ["a"; "a"; "a"; "a"; "b"; "c"; "c"; "a"; "a"; "d"; "e"; "e"; "e"; "e"];;
-> [Many (4, "a"); One "b"; Many (2, "c"); Many (2, "a"); One "d"; Many (4, "e")]
*)

(* ---------------------------------------------------------------------------------------------- *)

(*
12. Decode a run-length encoded list
     Given a run-length code list generated as specified in the previous problem, construct its uncompressed version
*)

let decode lst =
  let rec many count elem acc =
    if count = 0 then acc
    else many (count - 1) elem (elem :: acc)
  in
  let rec aux lst acc =
    match lst with
    | [] -> acc
    | One h :: t -> aux t (h :: acc)
    | Many (count, elem) :: t -> aux t (many count elem acc)
  in
  aux (List.rev lst) [];;

(*
decode [Many (4, "a"); One "b"; Many (2, "c"); Many (2, "a"); One "d"; Many (4, "e")];;
-> ["a"; "a"; "a"; "a"; "b"; "c"; "c"; "a"; "a"; "d"; "e"; "e"; "e"; "e"]
*)

(* ---------------------------------------------------------------------------------------------- *)

(*
12. Run-length encoding of a list (direct solution)
     Implement the so-called run-length encoding data compression method directly. I.e. don't explicitly create the sublists containing the duplicates, as in problem "Pack consecutive duplicates of list elements into sublists", but only count them. As in problem "Modified run-length encoding", simplify the result list by replacing the singleton lists (1 X) by X.
*)

let encode lst =
  let rle count x = if count = 0 then One x else Many (count + 1, x) in
  let rec aux lst count acc =
    match lst with
    | [] -> [] (* Can only be reached if original list is empty *)
    | [x] -> rle count x :: acc
    | a :: (b :: _ as t) -> if a = b then aux t (count + 1) acc
                            else aux t 0 (rle count a :: acc)
  in
    List.rev (aux lst 0 []);;

(*
encode ["a";"a";"a";"a";"b";"c";"c";"a";"a";"d";"e";"e";"e";"e"];;
-> [Many (4, "a"); One "b"; Many (2, "c"); Many (2, "a"); One "d"; Many (4, "e")]
*)

(* ---------------------------------------------------------------------------------------------- *)

(*
13. Duplicate the elements of a list
*)

(* Not tail recursive *)
let rec duplicate lst =
  match lst with
  | [] -> []
  | h :: t -> h :: h :: duplicate t;;

(* Tail recursive *)
let duplicate lst =
  let rec aux lst acc =
    match lst with
    | [] -> acc
    | h :: t -> aux t (h :: h :: acc)
  in
   aux (List.rev lst) [];;

(*
duplicate ["a"; "b"; "c"; "c"; "d"];;
-> ["a"; "a"; "b"; "b"; "c"; "c"; "c"; "c"; "d"; "d"]
*)

(* ---------------------------------------------------------------------------------------------- *)

(*
14. Replicate the elements of a list a given number of times
*)

let replicate lst n =
  let rec repl elem n acc =
    if n = 0 then acc
    else repl elem (n - 1) (elem :: acc)
  in
  let rec aux lst acc =
    match lst with
    | [] -> acc
    | h :: t -> aux t (repl h n acc)
  in
  aux (List.rev lst) [];;

(*
`aux (List.rev lst) [];;` is more efficient compared to `List.rev (aux lst [])`
because the output list could be much longer compared to the input list!
*)

(*
replicate ["a"; "b"; "c"] 3;;
-> ["a"; "a"; "a"; "b"; "b"; "b"; "c"; "c"; "c"]
*)

(* ---------------------------------------------------------------------------------------------- *)
