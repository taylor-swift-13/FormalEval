Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.

Definition truncate_number_spec (number : R) (decimal : R) : Prop :=
  0 <= number /\
  exists z : Z,
    IZR z <= number < IZR z + 1 /\
    decimal = number - IZR z.