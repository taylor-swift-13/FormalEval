
Require Import ZArith.
Require Import String.

Definition multiply_spec (a : Z) (b : Z) (product : Z) : Prop :=
  product = (a mod 10) * (b mod 10).
