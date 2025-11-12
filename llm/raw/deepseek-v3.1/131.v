
Require Import ZArith.
Require Import String.
Require Import List.
Import ListNotations.

Definition digits_spec (n : Z) (result : Z) : Prop :=
  (n > 0) -> 
  (let digits := map (fun ch => Z.of_nat (Nat.of_ascii ch - 48)) (list_ascii_of_string (Z.to_string n)) in
   let odd_digits := filter (fun d => Z.odd d) digits in
   result = if odd_digits = [] then 0 else fold_left Z.mul odd_digits 1).
