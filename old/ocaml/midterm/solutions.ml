(*
1. Data una lista di interi una sequenza è data da numeri consecutivi nella lista e si chiude con uno o più zeri.
Restituire una lista con le somme delle sequenze.

Esempio: [1; 2; 3; 0; 4; 5; 0; 0; 1; 0] -> [6; 9; 1]
*)

let aggregator lst =
  let rec aggregator lst acc out =
    match lst with
    | [] -> out
    | h :: t when h = 0 ->
        let reduced = List.fold_left (fun x y -> x + y) 0 acc in
        if reduced = 0 then
          aggregator t [] out
        else
          aggregator t [] (reduced :: out)
    | h :: t -> aggregator t (h :: acc) out
  in
  List.rev (aggregator lst [] [])

(* -------------------------------------- *)

(*
2. Data una lista di interi ritorna una seconda lista composta dal numero di occorrenze consecutive nella prima lista.

Esempio: [8; 8; 8; 8; 1; 1; 2; 4; 4; 4; 5] -> [4; 2; 1; 3; 1]
*)

let occurrences lst =
  let rec occurrences lst acc out =
    match lst with
    | [] -> out
    | [ a ] -> acc :: out
    | a :: b :: t when a = b -> occurrences (b :: t) (acc + 1) out
    | a :: b :: t -> occurrences (b :: t) 1 (acc :: out)
  in
  List.rev (occurrences lst 1 [])
