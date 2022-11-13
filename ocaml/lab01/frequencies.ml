let word_frequency filename =
  let re = Str.regexp "[^a-zA-Z]+" in
  let ht = Hashtbl.create 100 in
  let ic = open_in filename in
  try
    while true do
      let line = input_line ic in
      let words = Str.split re line in
      List.iter
        (fun word ->
          let lc_word = String.lowercase_ascii word in
          match Hashtbl.find_opt ht lc_word with
          | None -> Hashtbl.add ht lc_word 1
          | Some counter -> Hashtbl.replace ht lc_word (counter + 1))
        words
    done;
    ht
  with End_of_file ->
    close_in ic;
    ht

let right_pad str =
  let str_len = String.length str in
  if str_len < 15 then
    str ^ String.make (15 - str_len) ' '
  else
    str

let print_frequencies ht =
  (* Example: lst -> [("apple", 2); ("banana", 4); ("kiwi", 3); ...] *)
  let lst = Hashtbl.fold (fun word count acc -> (word, count) :: acc) ht [] in
  let sorted_lst = List.sort (fun (_, c1) (_, c2) -> compare c2 c1) lst in
  Printf.printf "WORD            COUNT\n";
  List.iter
    (fun (word, count) -> Printf.printf "%s %d\n" (right_pad word) count)
    sorted_lst
;;

print_frequencies (word_frequency "freq.txt")
