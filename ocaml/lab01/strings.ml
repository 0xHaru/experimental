(* 1. *)
let explode str =
  let rec expl str i lst =
    if i < 0 then
      lst
    else
      expl str (i - 1) (str.[i] :: lst)
  in
  expl str (String.length str - 1) []

let is_letter ch =
  match ch with
  | 'a' .. 'z' -> true
  | 'A' .. 'Z' -> true
  | _ -> false

let is_palindrome str =
  let lowercase_str = String.lowercase_ascii str in
  let char_lst = explode lowercase_str in
  let letters = List.filter is_letter char_lst in
  letters = List.rev letters
;;

Printf.printf "Palindromes:\n";
Printf.printf "  detartrated - %b\n" (is_palindrome "detartrated");
Printf.printf "  Do geese see God? - %b\n" (is_palindrome "Do geese see God?");
Printf.printf "  Rise to vote, sir. - %b\n" (is_palindrome "Rise to vote, sir.");
Printf.printf "  This is a test - %b\n\n" (is_palindrome "This is a test")

(* 2. *)
let implode lst =
  let rec impl lst str =
    match lst with
    | [] -> str
    | h :: t -> impl t (str ^ String.make 1 h)
  in
  impl lst ""

let ( - ) str1 str2 =
  let lst1 = explode str1 in
  let lst2 = explode str2 in
  let filtered = List.filter (fun ch -> not (List.mem ch lst2)) lst1 in
  implode filtered
;;

Printf.printf "Operator ( - ):\n";
Printf.printf "  Walter Cazzola - abcwxyz = %s\n\n" ("Walter Cazzola" - "abcwxyz")

(* 3. *)
let anagram str lst =
  let str_sort str = explode str |> List.sort compare |> implode in
  let sorted_str = str_sort str in
  let mapped_lst = List.map str_sort lst in
  List.mem sorted_str mapped_lst
;;

Printf.printf "Anagrams:\n";

let result = anagram "restful" [ "functional"; "programming"; "fluster" ] in
Printf.printf "  restful -> [functional; programming; fluster] - %b\n" result;

let result = anagram "restful" [ "functional"; "programming"; "cluster" ] in
Printf.printf "  restful -> [functional; programming; cluster] - %b\n" result
