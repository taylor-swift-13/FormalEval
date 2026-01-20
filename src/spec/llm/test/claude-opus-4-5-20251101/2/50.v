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

Definition R3_111878426342652 : R := 3111878426342652 / 1000000000000000.
Definition R0_11187842634265222 : R := 111878426342652 / 1000000000000000.

Example truncate_test : truncate_number_spec R3_111878426342652 R0_11187842634265222.
Proof.
  unfold truncate_number_spec, R3_111878426342652, R0_11187842634265222.
  split.
  - lra.
  - exists 3%Z.
    split.
    + simpl.
      split; lra.
    + split.
      * simpl. lra.
      * lra.
Qed.