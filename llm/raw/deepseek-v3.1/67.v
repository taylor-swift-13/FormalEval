
Require Import ZArith.
Require Import String.
Require Import List.

Definition fruit_distribution_spec (s : string) (n : Z) (result : Z) : Prop :=
  exists words : list string,
  words = String.split " " s ∧
  length words >= 4 ∧
  (∃ c1 c2 : Z,
    c1 = Z.of_string (nth 0 words ""%string) ∧
    c2 = Z.of_string (nth 3 words ""%string) ∧
    n - c1 - c2 >= 0 ∧
    result = n - c1 - c2).
