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

Definition R3_33346058589665 : R := 333346058589665 / 100000000000000.
Definition R0_33346058589664995 : R := 33346058589664995 / 100000000000000000.

Example truncate_test : truncate_number_spec R3_33346058589665 (R3_33346058589665 - 3).
Proof.
  unfold truncate_number_spec, R3_33346058589665.
  split.
  - lra.
  - exists 3%Z.
    split.
    + simpl.
      split; lra.
    + split.
      * simpl. lra.
      * simpl. lra.
Qed.