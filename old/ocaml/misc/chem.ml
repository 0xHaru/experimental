(*
Exercise 1: SOLVED
  Put into a list, called alkaline_earth_metals, the atomic numbers of the six alkaline earth metals: beryllium (4), magnesium (12), calcium (20), strontium (38), barium (56), and radium (88). Then

    1. Write a function that returns the highest atomic number in alkaline_earth_metals.
    2. Write a function that sorts alkaline_earth_metals in ascending order (from the lightest to the heaviest).

  Put into a second list, called noble_gases, the noble gases: helium (2), neon (10), argon (18), krypton (36), xenon (54), and radon (86). Then

    3. Write a function (or a group of functions) that merges the two lists and print the result as couples (name, atomic number) sorted in ascending order on the element names.
*)

(* ---------------------------------------------------------------------------------------------- *)

(* 1. *)

(* List of integers *)

let rec max1 list =
  match list with
  | [] -> -1
  | [ x ] -> x
  | h :: t -> max h (max1 t);;

let rec max2 list =
  let max_int x y =
    if x > y then x else y
  in
  match list with
  | [] -> -1
  | [ x ] -> x
  | h :: t -> max_int h (max2 t);;

(* x :: [] == [ x ] *)
let rec max3 list =
  match list with
  | [] -> -1
  | x :: [] -> x
  | h :: t ->
      let m = max3 t in
      if h > m then h else m;;

let alkaline_earth_metals = [4; 12; 20; 38; 56; 88];;
Printf.printf "1. with list of integers\n";;
Printf.printf "%d\n" (max1 alkaline_earth_metals);; (* Output: 88 *)
Printf.printf "%d\n" (max2 alkaline_earth_metals);; (* Output: 88 *)
Printf.printf "%d\n\n" (max3 alkaline_earth_metals);; (* Output: 88 *)

(* List of tuples *)

let rec max4 list =
  match list with
  | [] -> -1
  | [ (name, number) ] -> number
  | (name, number) :: t -> max number (max4 t);;

let alkaline_earth_metals = [
  ("beryllium", 4);
  ("magnesium", 12);
  ("calcium",   20);
  ("strontium", 38);
  ("barium",    56);
  ("radium",    88);
];;

Printf.printf "1. with list of tuples\n";;
Printf.printf "%d\n\n" (max4 alkaline_earth_metals);; (* Output: 88 *)

(* ---------------------------------------------------------------------------------------------- *)

(* 2. *)

(* https://codereview.stackexchange.com/questions/125571/recursive-bubble-sort-in-ocaml *)

(* List of integers *)

let rec bubble_sort list: int list =
  let sorted =
    match list with
    | [] -> []
    | [ x ] -> [ x ]
    | x :: y :: tail ->
        if x > y then
          y :: bubble_sort (x :: tail)
        else
          x :: bubble_sort (y :: tail)
  in
  if list = sorted then list else bubble_sort sorted;;

let compare2 x y = if x > y then 1 else -1;;

let alkaline_earth_metals = [4; 12; 20; 38; 56; 88];;

Printf.printf "2. with list of integers\n";;

(* Output: 4 12 20 38 56 88 *)
List.iter (Printf.printf "%d ") (bubble_sort alkaline_earth_metals);;
Printf.printf "\n";;

(* Output: 4 12 20 38 56 88 *)
List.iter (Printf.printf "%d ") (List.sort compare alkaline_earth_metals);;
Printf.printf "\n";;

(* Output: 4 12 20 38 56 88 *)
List.iter (Printf.printf "%d ") (List.sort compare2 alkaline_earth_metals);;
Printf.printf "\n\n";;

(* List of tuples *)

let compare_tuples (name1, num1) (name2, num2) =
  if num1 > num2 then 1 else -1;;

let rec map f lst =
  match lst with
  | [] -> ()
  | h :: t -> f h; map f t;;

let print_element (name, num) = Printf.printf "(%s, %d)\n" name num;;

let alkaline_earth_metals = [
  ("beryllium", 4);
  ("magnesium", 12);
  ("calcium",   20);
  ("strontium", 38);
  ("barium",    56);
  ("radium",    88);
];;

Printf.printf "2. with list of tuples\n";;
map print_element (List.sort compare_tuples alkaline_earth_metals);;
(*
Output:
  (beryllium, 4)
  (magnesium, 12)
  (calcium, 20)
  (strontium, 38)
  (barium, 56)
  (radium, 88)
*)

Printf.printf "\n";;

(* ---------------------------------------------------------------------------------------------- *)

(* 3. *)

(* List of records *)

type element = {
  name: string;
  number: int;
};;

let concat l1 l2 =
  let rec loop l1 l2 acc =
    match l1, l2 with
    | [], [] -> List.rev acc
    | [], h :: t -> loop [] t (h :: acc)
    | h :: t, l -> loop t l (h :: acc)
    in
    loop l1 l2 [];;

let rec map f lst =
  match lst with
  | [] -> ()
  | h :: t -> f h; map f t;;

let print_element e = Printf.printf "(%s, %d)\n" e.name e.number;;

let compare_records x y = compare x.name y.name;;

let alkaline_earth_metals = [
  {name = "beryllium"; number = 4};
  {name = "magnesium"; number = 12};
  {name = "calcium";   number = 20};
  {name = "strontium"; number = 38};
  {name = "barium";    number = 56};
  {name = "radium";    number = 88};
];;

let noble_gases = [
  {name = "helium";  number = 2};
  {name = "neon";    number = 10};
  {name = "argon";   number = 18};
  {name = "krypton"; number = 36};
  {name = "xenon";   number = 54};
  {name = "radon";   number = 86};
];;

let merged = concat alkaline_earth_metals noble_gases;;
Printf.printf "3. with list of records\n";;
map print_element (List.sort compare_records merged);;
(*
Output:
  (argon, 18)
  (barium, 56)
  (beryllium, 4)
  (calcium, 20)
  (helium, 2)
  (krypton, 36)
  (magnesium, 12)
  (neon, 10)
  (radium, 88)
  (radon, 86)
  (strontium, 38)
  (xenon, 54)
*)

Printf.printf "\n";;

(* List of tuples *)

let concat l1 l2 =
  let rec loop l1 l2 acc =
    match l1, l2 with
    | [], [] -> List.rev acc
    | [], h :: t -> loop [] t (h :: acc)
    | h :: t, l -> loop t l (h :: acc)
    in
    loop l1 l2 [];;

let rec map f lst =
  match lst with
  | [] -> ()
  | h :: t -> f h; map f t;;

let print_element (name, number) = Printf.printf "(%s, %d)\n" name number;;

let compare_tuples (name1, num1) (name2, num2) = compare name1 name2;;

let alkaline_earth_metals = [
  ("beryllium", 4);
  ("magnesium", 12);
  ("calcium",   20);
  ("strontium", 38);
  ("barium",    56);
  ("radium",    88);
];;

let noble_gases = [
  ("helium",  2);
  ("neon",    10);
  ("argon",   18);
  ("krypton", 36);
  ("xenon",   54);
  ("radon",   86);
];;

let merged = concat alkaline_earth_metals noble_gases;;
Printf.printf "3. with list of tuples\n";;
map print_element (List.sort compare_tuples merged);;
(*
Output:
  (argon, 18)
  (barium, 56)
  (beryllium, 4)
  (calcium, 20)
  (helium, 2)
  (krypton, 36)
  (magnesium, 12)
  (neon, 10)
  (radium, 88)
  (radon, 86)
  (strontium, 38)
  (xenon, 54)
*)
