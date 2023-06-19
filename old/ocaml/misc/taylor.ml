(*
Exercise 6:
                                                         x^3   x^5   x^7
  sin(x) can be approximated by the Taylor's series: x - --- + --- - --- + ...
                                                          3!    5!    7!

  Similarly you can approximate all the trigonometric and transcendent functions (look at:http://en.wikipedia.org/wiki/Taylor_series).

  Let's write a module to implement sin x n by using the Taylor's series (where n is the level of approximation, i.e., 1 only one item, 2 two items, 3 three items and so on). Do the same with cosine, tangent, logarithm and so on.

  Let's compare your functions with those implemented in the pervasive module at the growing of the approximation level.
*)

(* Links:
     - https://stackoverflow.com/a/15256237
*)

(* ---------------------------------------------------------------------------------------------- *)


module Taylor = struct
  let rec factorial n =
    if n <= 1.0 then 1.0 else n *. factorial (n -. 1.0);;

  let sin x n =
    let rec aux x n k acc =
      if k <= n then
        let num = (-1.0 ** k) *. (x ** (1.0 +. 2.0 *. k)) in
        let denum = factorial (1.0 +. 2.0 *. k) in
        let term = num /. denum in
        aux x n (k +. 1.0) (term +. acc)
      else
        acc
    in
    aux x n 0.0 0.0;;
end;;

Printf.printf "%f\n" (Taylor.sin 1.0 1.0);;
