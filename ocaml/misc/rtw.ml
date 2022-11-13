(* Reinventing the wheel! *)

(* Tail recursive *)
let filter func lst =
  let rec aux f in_lst out_lst =
    match in_lst with
    | [] -> out_lst
    | h :: t ->
      if f h then
        aux f t (h :: out_lst)
      else
        aux f t out_lst
  in
  List.rev (aux func lst []);;

(* Not tail recursive *)
let rec filter func lst =
  match lst with
  | [] -> []
  | h :: t ->
    if func h then
      h :: filter func t
    else
      filter func t;;

(* ---------------------------------------------------------------------------------------------- *)

(* Tail recursive *)
let map func lst =
  let rec map func lst acc =
    match lst with
    | [] -> acc
    | h :: t -> map func t ((func h) :: acc)
  in
  List.rev (map func lst []);;

(* Not tail recursive *)
let rec map func lst =
  match lst with
  | [] -> []
  | h :: t -> func h :: map func t;;

(* ---------------------------------------------------------------------------------------------- *)

(* Tail recursive *)
let rec reduce func acc lst =
  match lst with
  | [] -> acc
  | h :: t -> reduce func (func h acc) t;;
