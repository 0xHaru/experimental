(*
Exercise 2: SOLVED
  Beyond the well-known Celsius and Fahrenheit, there are other six temperature scales: Kelvin, Rankine, Delisle, Newton, Réaumur, and Rømer (Look at: http://en.wikipedia.org/wiki/Comparison_of_temperature_scales to read about them).

    1. Write a function that given a pure number returns a conversion table for it among any of the 8 scales.
    2. Write a function that given a temperature in a specified scale returns a list of all the corresponding temperatures in the other scales, note that the scale must be specified.

  Hint: Define a proper datatype for the temperature.
*)

(* ---------------------------------------------------------------------------------------------- *)

type unit_t = Celsius | Fahrenheit | Kelvin | Rankine | Delisle | Newton | Reaumur | Romer;;
type temp_t = {
  unit_: unit_t;
  value: float
};;

let any_to_celsius temp: temp_t =
  match temp.unit_ with
  | Celsius    -> temp
  | Fahrenheit -> { unit_ = Fahrenheit; value = ((temp.value -. 32.0) *. (5.0 /. 9.0))   }
  | Kelvin     -> { unit_ = Kelvin;     value = (temp.value -. 273.15)                   }
  | Rankine    -> { unit_ = Rankine;    value = ((temp.value -. 491.67) *. (5.0 /. 9.0)) }
  | Delisle    -> { unit_ = Delisle;    value = (100.0 -. temp.value *. (2.0 /. 3.0))    }
  | Newton     -> { unit_ = Newton;     value = (temp.value *. (100.0 /. 33.0))          }
  | Reaumur    -> { unit_ = Reaumur;    value = (temp.value *. (5.0 /. 4.0))             }
  | Romer      -> { unit_ = Romer;      value = ((temp.value -. 7.5) *. (40.0 /. 21.0))  };;

let celsius_to_any (temp: temp_t) (unit_: unit_t) =
  match unit_ with
  | Celsius    -> temp
  | Fahrenheit -> { unit_ = Fahrenheit; value = (temp.value *. (9.0 /. 5.0) +. 32.0)     }
  | Kelvin     -> { unit_ = Kelvin;     value = (temp.value +. 273.15)                   }
  | Rankine    -> { unit_ = Rankine;    value = ((temp.value +. 273.15) *. (9.0 /. 5.0)) }
  | Delisle    -> { unit_ = Delisle;    value = ((100.0 -. temp.value) *. 1.5)           }
  | Newton     -> { unit_ = Newton;     value = (temp.value *. (33.0 /. 100.0))          }
  | Reaumur    -> { unit_ = Reaumur;    value = (temp.value *. (4.0 /. 5.0))             }
  | Romer      -> { unit_ = Romer;      value = (temp.value *. (21.0 /. 40.0) +. 7.5)    };;

let string_of_unit_t unit_ =
  match unit_ with
  | Celsius    -> "Celsius"
  | Fahrenheit -> "Fahrenheit"
  | Kelvin     -> "Kelvin"
  | Rankine    -> "Rankine"
  | Delisle    -> "Delisle"
  | Newton     -> "Newton"
  | Reaumur    -> "Reaumur"
  | Romer      -> "Romer";;

let abbr_of_unit_t unit_ =
    match unit_ with
    | Celsius    -> "Cel"
    | Fahrenheit -> "Fah"
    | Kelvin     -> "Kel"
    | Rankine    -> "Ran"
    | Delisle    -> "Del"
    | Newton     -> "New"
    | Reaumur    -> "Rea"
    | Romer      -> "Rom";;

(* let print_temp temp = Printf.printf "Unit: %s - Value: %F\n" (string_of_unit_t temp.unit_) temp.value;; *)
(* let t = { unit_ = Celsius; value = 500.00 };; *)
(* print_temp (any_to_celsius t);; *)
(* print_temp (celsius_to_any t Romer);; *)

(* ---------------------------------------------------------------------------------------------- *)

(* 1. *)

let left_pad str =
  let str_len = String.length str in
  if str_len < 10 then
    (String.make (10 - str_len) ' ') ^ str
  else
    str;;

let row_maker temp =
  let rec aux t cols =
    match cols with
    | [] -> ()
    | cols_head :: cols_tail ->
      let converted = (celsius_to_any (any_to_celsius t) cols_head).value in
      let converted_str = (Printf.sprintf "%.2f" converted) in
      Printf.printf "%s  " (left_pad converted_str);
      aux t cols_tail
  in
  let units = [Celsius; Fahrenheit; Kelvin; Rankine; Delisle; Newton; Reaumur; Romer] in
  aux temp units;;

let conversion_table pure_n =
  let rec aux n rows =
    match rows with
    | [] -> ()
    | rows_head :: rows_tail ->
        Printf.printf "\n%s" (abbr_of_unit_t rows_head);
        row_maker { unit_ = rows_head; value = pure_n };
        aux n rows_tail
  in
  let () = Printf.printf "          Cel         Fah         Kel         Ran         Del         New         Rea         Rom" in
  let units = [Celsius; Fahrenheit; Kelvin; Rankine; Delisle; Newton; Reaumur; Romer] in
  aux pure_n units;;

conversion_table 42.0;;
Printf.printf "\n";;
(*
Output:
          Cel         Fah         Kel         Ran         Del         New         Rea         Rom
Cel     42.00      107.60      315.15      567.27       87.00       13.86       33.60       29.55
Fah      5.56       42.00      278.71      501.67      141.67        1.83        4.44       10.42
Kel   -231.15     -384.07       42.00       75.60      496.72      -76.28     -184.92     -113.85
Ran   -249.82     -417.67       23.33       42.00      524.73      -82.44     -199.85     -123.65
Del     72.00      161.60      345.15      621.27       42.00       23.76       57.60       45.30
New    127.27      261.09      400.42      720.76      -40.91       42.00      101.82       74.32
Rea     52.50      126.50      325.65      586.17       71.25       17.32       42.00       35.06
Rom     65.71      150.29      338.86      609.96       51.43       21.69       52.57       42.00
*)

(* ---------------------------------------------------------------------------------------------- *)

(* 2. *)

let conversion_list temp =
  let rec aux t cols =
    match cols with
    | [] -> ()
    | cols_head :: cols_tail ->
      let converted = (celsius_to_any (any_to_celsius t) cols_head).value in
      let converted_str = (Printf.sprintf "%.2f" converted) in
      Printf.printf "%s°%s | " converted_str (abbr_of_unit_t cols_head);
      aux t cols_tail
  in
  Printf.printf "%.2f°%s -> " temp.value (abbr_of_unit_t temp.unit_);
  let units = [Celsius; Fahrenheit; Kelvin; Rankine; Delisle; Newton; Reaumur; Romer] in
  aux temp units;;

Printf.printf "\n";;
conversion_list { unit_ = Celsius; value = 42.0 };;
Printf.printf "\n";;
(*
Output:
42.00°Cel -> 42.00°Cel | 107.60°Fah | 315.15°Kel | 567.27°Ran | 87.00°Del | 13.86°New | 33.60°Rea | 29.55°Rom |
*)
