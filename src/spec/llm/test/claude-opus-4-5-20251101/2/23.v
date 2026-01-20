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

Definition R1_7558893686701653 : R := 1 + 7558893686701653 / 10000000000000000.
Definition R0_7558893686701653 : R := 7558893686701653 / 10000000000000000.

Example truncate_test : truncate_number_spec R1_7558893686701653 R0_7558893686701653.
Proof.
  unfold truncate_number_spec, R1_7558893686701653, R0_7558893686701653.
  split.
  - lra.
  - exists 1%Z.
    split.
    + simpl.
      split; lra.
    + split.
      * simpl. lra.
      * lra.
Qed.