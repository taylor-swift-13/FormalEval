
Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Psatz.
Import ListNotations.

Definition poly_spec (xs : list R) (x : R) (res : R) : Prop :=
  res = fold_right (fun '(i, coeff) acc => acc + coeff * x ^ i) 0 (combine (seq 0 (length xs)) xs).

Definition find_zero_spec (xs : list R) (x : R) : Prop :=
  length xs mod 2 = 0 /\
  exists n coeff_n,
    nth_error xs n = Some coeff_n /\
    coeff_n <> 0 /\
    (forall m coeff_m, nth_error xs m = Some coeff_m -> m > n -> coeff_m = 0) /\
  poly_spec xs x 0.
