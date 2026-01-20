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

Definition R5_99 : R := 5 + 99/100.
Definition R0_99 : R := 99/100.

Example truncate_test : truncate_number_spec R5_99 R0_99.
Proof.
  unfold truncate_number_spec, R5_99, R0_99.
  split.
  - lra.
  - exists 5%Z.
    split.
    + simpl.
      split; lra.
    + split.
      * simpl. lra.
      * lra.
Qed.