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

Definition R10_340562837282636 : R := 10340562837282636 / 1000000000000000.
Definition R0_34056283728263637 : R := 340562837282636 / 1000000000000000.

Example truncate_test : truncate_number_spec R10_340562837282636 R0_34056283728263637.
Proof.
  unfold truncate_number_spec, R10_340562837282636, R0_34056283728263637.
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