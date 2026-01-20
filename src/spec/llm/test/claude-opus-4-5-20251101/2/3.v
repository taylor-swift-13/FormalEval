Require Import Reals.
Require Import Floats.
Require Import ZArith.
Require Import Lra.
Open Scope R_scope.

Definition truncate_number_spec (number : R) (result : R) : Prop :=
  number > 0 /\
  exists (int_part : Z), 
    IZR int_part <= number < IZR (int_part + 1) /\
    result = number - IZR int_part /\
    0 <= result < 1.

Definition R123_456 : R := 123456 / 1000.
Definition R0_456 : R := 456 / 1000.

Example truncate_test : truncate_number_spec R123_456 R0_456.
Proof.
  unfold truncate_number_spec, R123_456, R0_456.
  split.
  - lra.
  - exists 123%Z.
    split.
    + simpl.
      split; lra.
    + split.
      * simpl. lra.
      * lra.
Qed.