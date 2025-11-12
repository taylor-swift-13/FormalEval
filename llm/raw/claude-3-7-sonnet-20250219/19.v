
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Definition digit_str := string.

Definition to_int (d : digit_str) : option nat :=
  if String.eqb d "zero" then Some 0 else
  if String.eqb d "one" then Some 1 else
  if String.eqb d "two" then Some 2 else
  if String.eqb d "three" then Some 3 else
  if String.eqb d "four" then Some 4 else
  if String.eqb d "five" then Some 5 else
  if String.eqb d "six" then Some 6 else
  if String.eqb d "seven" then Some 7 else
  if String.eqb d "eight" then Some 8 else
  if String.eqb d "nine" then Some 9 else None.

Definition sort_numbers_spec (input output : string) : Prop :=
  exists digits ints sorted_ints,
    (* input is tokenized by spaces into digits *)
    input = String.concat " " digits /\
    (* all digits are valid numeral strings *)
    Forall (fun d => to_int d <> None) digits /\
    (* map digits to ints *)
    map to_int digits = map (@Some nat) ints /\
    (* sorted_ints is ints sorted in ascending order *)
    sorted_ints = List.sort Nat.leb ints /\
    (* output is space-joined sorted numerals by their string form *)
    output = String.concat " " (map (fun i =>
      match i with
      | 0 => "zero" | 1 => "one" | 2 => "two" | 3 => "three" | 4 => "four"
      | 5 => "five" | 6 => "six" | 7 => "seven" | 8 => "eight" | 9 => "nine"
      | _ => "" (* unreachable *)
      end) sorted_ints).
