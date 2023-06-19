let rec reduce func acc lst =
  match lst with
  | [] -> acc
  | h :: t -> reduce func (func h acc) t;;

List.fold_left (fun x y -> x - y) 0 [1;2;3;4;5];; (* -15 *)
reduce (fun x y -> y - x) 0 [1;2;3;4;5];; (* -15 *)

List.fold_right (fun x y -> x - y) [1;2;3;4;5] 0;; (* 3 *)
reduce (fun x y -> x - y) 0 [1;2;3;4;5];; (* 3 *)


(*
-15 -> (((((0 - 1) - 2) - 3) - 4) - 5)
3   -> (1 - (2 - (3 - (4 - (5 - 0)))))
*)


(** Returns the number of occurences of a given element in the list *)
let occurences (lst : 'a list) (el : 'a) : int =
   let rec occ (lst : 'a list) (el : 'a) (acc : int) : int =
     match lst with
     | [] -> acc
     | h :: t ->
         if h = el then
           occ t el (acc + 1)
         else
           occ t el acc
   in
   occ lst el 0
