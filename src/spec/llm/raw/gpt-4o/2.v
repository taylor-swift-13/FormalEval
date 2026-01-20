
Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.

Definition truncate_number_spec (number : R) (decimal_part : R) : Prop :=
  number >= 0 /\ decimal_part = number - IZR (Z.floor number).
