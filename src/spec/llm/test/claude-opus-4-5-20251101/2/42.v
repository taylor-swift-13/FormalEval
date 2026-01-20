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

Definition R_input : R := 8694186154267374 / 10000000000000000.
Definition R_output : R := 8694186154267374 / 10000000000000000.

Example truncate_test : truncate_number_spec R_input R_output.
Proof.
  unfold truncate_number_spec, R_input, R_output.
  split.
  - lra.
  - exists 0%Z.
    split.
    + simpl.
      split; lra.
    + split.
      * simpl. lra.
      * lra.
Qed.