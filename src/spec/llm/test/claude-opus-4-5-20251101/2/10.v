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

Definition R500_00678 : R := 500 + 678 / 100000.
Definition R0_00678 : R := 678 / 100000.

Example truncate_test : truncate_number_spec R500_00678 R0_00678.
Proof.
  unfold truncate_number_spec, R500_00678, R0_00678.
  split.
  - lra.
  - exists 500%Z.
    split.
    + simpl.
      split; lra.
    + split.
      * simpl. lra.
      * lra.
Qed.