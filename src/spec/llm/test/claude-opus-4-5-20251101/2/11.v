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

Definition R11_11 : R := 11 + 11/100.
Definition R0_11 : R := 11/100.

Example truncate_test : truncate_number_spec R11_11 R0_11.
Proof.
  unfold truncate_number_spec, R11_11, R0_11.
  split.
  - lra.
  - exists 11%Z.
    split.
    + simpl.
      split; lra.
    + split.
      * simpl. lra.
      * lra.
Qed.