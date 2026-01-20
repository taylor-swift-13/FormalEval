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

Definition R10_291122396192739 : R := 10291122396192739 / 1000000000000000.
Definition R0_2911223961927387 : R := 2911223961927387 / 10000000000000000.

Example truncate_test : truncate_number_spec R10_291122396192739 R0_2911223961927387.
Proof.
  unfold truncate_number_spec, R10_291122396192739, R0_2911223961927387.
  split.
  - lra.
  - exists 10%Z.
    split.
    + simpl.
      split; lra.
    + split.
      * simpl. lra.
      * lra.
Qed.