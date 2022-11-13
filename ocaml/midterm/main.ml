open Printf
open Solutions

let main () =
  printf "1: "; aggregator [1; 2; 3; 0; 4; 5; 0; 0; 1; 0] |> List.iter (printf "%d ");
  printf "\n2: "; aggregator [1; 0] |> List.iter (printf "%d ");
  printf "\n3: "; aggregator [0; 0] |> List.iter (printf "%d ");
  printf "\n4: "; aggregator [0] |> List.iter (printf "%d ");
  printf "\n5: "; aggregator [] |> List.iter (printf "%d ");

  printf "\n6: "; occurrences [8; 8; 8; 8; 1; 1; 2; 4; 4; 4; 5] |> List.iter (printf "%d ");
  printf "\n7: "; occurrences [8; 5; 5] |> List.iter (printf "%d ");
  printf "\n8: "; occurrences [8] |> List.iter (printf "%d ");
  printf "\n9: "; occurrences [] |> List.iter (printf "%d ");;

main ();
printf "\n"

(*
ocamlc -o main solutions.ml main.ml
*)
