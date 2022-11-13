(*
Exercise 3: NOT SOLVED
  Write the matrix datatype with the following operations:
    1. A function zeroes to construct a matrix of size n×m filled with zeros.
    2. A function identity to construct the identity matrix (the one with all 0s but the 1s on the diagonal) of given size.
    3. A function init to construct a square matrix of a given size n filled with the first n×n integers.
    4. A function transpose that transposes a generic matrix independently of its size and content.
    5. The basics operators + and * that adds and multiplies two matrices non necessarily squared.
*)

(* ---------------------------------------------------------------------------------------------- *)

(* type matrix_t = int array array *)

let print_matrix matrix =
  let rows = Array.length matrix in
  let cols = Array.length matrix.(0) in
  for i = 0 to rows - 1 do
    for j = 0 to cols - 1 do
      Printf.printf "%d " matrix.(i).(j)
    done;
    Printf.printf "\n"
  done;;

(* ---------------------------------------------------------------------------------------------- *)

(* 1. *)

(* let zeroes rows cols = Array.make rows (Array.make cols 0) *)
let zeroes rows cols = Array.make_matrix rows cols 0;;
print_matrix (zeroes 5 5);;
(*
Output:
  0 0 0 0 0
  0 0 0 0 0
  0 0 0 0 0
  0 0 0 0 0
  0 0 0 0 0
*)

Printf.printf "\n";;

(* ---------------------------------------------------------------------------------------------- *)

(* 2. *)

let identity rows cols =
  let matrix = zeroes rows cols in
  for i = 0 to rows - 1 do
    matrix.(i).(i) <- 1
  done;
  matrix;;

print_matrix (identity 5 5);;
(*
Output:
  1 0 0 0 0
  0 1 0 0 0
  0 0 1 0 0
  0 0 0 1 0
  0 0 0 0 1
*)

Printf.printf "\n";;

(* ---------------------------------------------------------------------------------------------- *)

(* 3. *)

let init n =
  let acc = ref 0 in
  let matrix = zeroes n n in
  for i = 0 to n - 1 do
    for j = 0 to n - 1 do
      matrix.(i).(j) <- !acc;
      acc := !acc + 1
    done;
  done;
  matrix;;

print_matrix (init 5);;
(*
Output:
  0 1 2 3 4
  5 6 7 8 9
  10 11 12 13 14
  15 16 17 18 19
  20 21 22 23 24
*)

Printf.printf "\n";;

(* ---------------------------------------------------------------------------------------------- *)

(* 4. *)

let transpose matrix =
  let rows = Array.length matrix in
  let cols = Array.length matrix.(0) in
  let t_matrix = zeroes cols rows in
  for i = 0 to rows - 1 do
    for j = 0 to cols - 1 do
      t_matrix.(j).(i) <- matrix.(i).(j)
    done;
  done;
  t_matrix;;

let matrix = [|[|1;2|];
               [|3;4|];
               [|5;6|]|];;
print_matrix (transpose matrix);;
(*
Output:
  1 3 5
  2 4 6
*)

Printf.printf "\n";;

(* ---------------------------------------------------------------------------------------------- *)

let add m1 m2 =
  if (Array.length m1 <> Array.length m2) ||
     (Array.length m1.(0) <> Array.length m2.(0)) then
    failwith "Two matrices must have an equal number of rows and columns to be added!";
  let rows = Array.length m1 in
  let cols = Array.length m1.(0) in
  let m3 = zeroes rows cols in
  for i = 0 to rows - 1 do
    for j = 0 to cols - 1 do
      m3.(i).(j) <- m1.(i).(j) + m2.(i).(j)
    done;
  done;
  m3;;

let m1 = [|[|1;3|];
           [|1;0|];
           [|1;2|]|];;
let m2 = [|[|0;0|];
           [|7;5|];
           [|2;1|]|];;

print_matrix (add m1 m2);;
(*
Output:
  1 3
  8 5
  3 3
*)

Printf.printf "\n";;

(* ---------------------------------------------------------------------------------------------- *)

let mult m1 m2 =
  if (Array.length m1.(0) <> Array.length m2) then
    failwith "The number of columns in the first matrix must be equal to the number of rows in the second matrix!";
  let rows1 = Array.length m1 in
  let rows2 = Array.length m2 in
  let cols2 = Array.length m2.(0) in
  let m3 = zeroes rows1 cols2 in
  for i = 0 to rows1 - 1 do
    for j = 0 to cols2 - 1 do
      let acc = ref 0 in
      for k = 0 to rows2 - 1 do
        acc := !acc + m1.(i).(k) * m2.(k).(j);
        if k = cols2 - 1 then m3.(i).(j) <- !acc;
      done;
    done;
  done;
  m3;;

let m1 = [|[|1;0;1|];
           [|2;1;1|];
           [|0;1;1|];
           [|1;1;2|]|];;
let m2 = [|[|1;2;1|];
           [|2;3;1|];
           [|4;2;2|];|];;

print_matrix (mult m1 m2);;
(*
Output:
  5 4 3
  8 9 5
  6 5 3
  11 9 6
*)
