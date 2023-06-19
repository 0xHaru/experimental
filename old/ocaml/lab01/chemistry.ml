open Printf

let alkaline_earth_metals =
  [
    ("beryllium", 4);
    ("magnesium", 12);
    ("calcium", 20);
    ("strontium", 38);
    ("barium", 56);
    ("radium", 88);
  ]

(* 1. *)
let rec max_atomic_num lst =
  match lst with
  | [] -> -1
  | [ (_, n) ] -> n
  | (_, n) :: t -> max n (max_atomic_num t)
;;

printf "%d\n" (max_atomic_num alkaline_earth_metals);;
printf "\n"

(* 2. *)
let sort_element_lst lst =
  let comp (_, num1) (_, num2) =
    if num1 > num2 then
      1
    else
      -1
  in
  List.sort comp lst

let print_element (name, num) = printf "(%s, %d)\n" name num;;

List.iter print_element (sort_element_lst alkaline_earth_metals);;
printf "\n"

(* 3. *)
let noble_gases =
  [
    ("helium", 2);
    ("neon", 10);
    ("argon", 18);
    ("krypton", 36);
    ("xenon", 54);
    ("radon", 86);
  ]

let rec merge lst1 lst2 =
  match lst1 with
  | [] -> lst2
  | h :: t -> merge t (h :: lst2)
;;

List.iter print_element (merge noble_gases alkaline_earth_metals |> sort_element_lst)
