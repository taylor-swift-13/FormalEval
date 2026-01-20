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

Definition R10_488539525905054 : R := 10488539525905054 / 1000000000000000.
Definition R0_488539525905054 : R := 488539525905054 / 1000000000000000.

Example truncate_test : truncate_number_spec R10_488539525905054 R0_488539525905054.
Proof.
  unfold truncate_number_spec, R10_488539525905054, R0_488539525905054.
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