
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Definition multiply_spec (a b product : Z) : Prop :=
  let unit_digit_a := Z.abs (a mod 10) in
  let unit_digit_b := Z.abs (b mod 10) in
  product = unit_digit_a * unit_digit_b.
