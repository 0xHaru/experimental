module type MatrixSig = sig
  type matrix

  val zeroes : int -> int -> matrix
  val identity : int -> int -> matrix
  val init : int -> matrix
  val transpose : matrix -> matrix
  val ( + ) : matrix -> matrix -> matrix
  val ( * ) : matrix -> matrix -> matrix
end

module Matrix = struct
  type matrix = int list list

  let zeroes rows cols = List.init rows (fun x -> List.init cols (fun y -> 0))

  let identity n =
    List.init n (fun x ->
        List.init n (fun y ->
            if x <> y then
              0
            else
              1))

  let init n = List.init n (fun x -> List.init n (fun y -> (x * n) + y + 1))

  let rec transpose m =
    match m with
    | [] -> []
    | [] :: _ -> []
    | rows -> List.map List.hd rows :: transpose (List.map List.tl rows)

  let ( + ) m1 m2 =
    List.map2 (fun x1 x2 -> List.map2 (fun y1 y2 -> y1 + y2) x1 x2) m1 m2
end

(*
DEBUGGING:

let identity n =
  List.init n (fun x ->
      Printf.printf "x: %d\n" x;
      List.init n (fun y ->
        Printf.printf "  y: %d\n" y;
        if x <> y then 0 else 1
      )
    )

let init n =
  List.init n (fun x ->
      Printf.printf "x: %d\n" x;
      List.init n (fun y ->
        Printf.printf "  y: %d\n" y;
        x * n + y + 1
      )
    )

let rec transpose matr =
  match matr with
  | [] ->
      Printf.printf "I shouldn't be here!\n";
      []
  | [] :: _ ->
      Printf.printf "[]\n";
      []
  | rows ->
      Printf.printf "[ ";
      List.iter (Printf.printf "%d ") (List.map List.hd rows);
      Printf.printf "] :: ";
      List.map List.hd rows :: transpose (List.map List.tl rows)

let ( + ) m1 m2 =
  List.map2 (fun x1 x2 ->
    Printf.printf "x1: [ "; List.iter (Printf.printf "%d ") x1;
    Printf.printf "] | ";
    Printf.printf "x2: [ "; List.iter (Printf.printf "%d ") x2;
    Printf.printf "]\n";
    List.map2 (fun y1 y2 ->
      Printf.printf "  y1: %d - y2: %d\n" y1 y2;
      y1 + y2)
    x1 x2)
  m1 m2
*)
