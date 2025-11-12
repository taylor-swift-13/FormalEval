
Require Import ZArith.
Require Import List.
Require Import String.
Require Import Ascii.

Definition strength (s : string) : Z :=
  let count_upper := List.length (List.filter (fun ch => (is_upper ch)) (list_ascii_of_string s)) in
  let count_lower := List.length (List.filter (fun ch => (is_lower ch)) (list_ascii_of_string s)) in
  Z.of_nat count_upper - Z.of_nat count_lower.

Definition Strongest_Extension_spec (class_name : string) (extensions : list string) (result : string) : Prop :=
  exists max_strength : Z,
    max_strength = list_max (map strength extensions) /\
    exists e : string,
      In e extensions /\
      strength e = max_strength /\
      (forall e' : string, In e' extensions -> strength e' = max_strength -> 
        exists index_e : nat, exists index_e' : nat,
          nth_error extensions index_e = Some e /\
          nth_error extensions index_e' = Some e' /\
          index_e <= index_e') /\
      result = class_name ++ "." ++ e.
