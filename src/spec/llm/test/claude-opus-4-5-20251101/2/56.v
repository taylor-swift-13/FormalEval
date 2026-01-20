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

Definition R_input : R := 0.9128948300399008.
Definition R_output : R := 0.9128948300399008.

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