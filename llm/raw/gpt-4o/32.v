
Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Definition poly_spec (xs : list R) (x : R) (result : R) : Prop :=
  result = fold_right Rplus 0 (map (fun '(coeff, i) => coeff * (x ^ i)) (combine xs (seq 0 (length xs)))).

Definition find_zero_spec (xs : list R) (x : R) : Prop :=
  (length xs mod 2 = 0) /\
  (exists coeff, coeff = nth (length xs - 1) xs 0 /\ coeff <> 0) /\
  poly_spec xs x 0.
