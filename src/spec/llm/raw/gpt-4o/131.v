
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Definition digits_spec (n : Z) (product : Z) : Prop :=
  let digits := map (fun ch => Z.of_nat (Nat.of_ascii ch)) (list_ascii_of_string (Z.to_string n)) in
  let odd_digits := filter (fun d => Z.odd d) digits in
  if odd_digits = [] then product = 0
  else product = fold_right Z.mul 1 odd_digits.
