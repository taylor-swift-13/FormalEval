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

Definition R999_99999 : R := 999 + 99999 / 100000.
Definition R0_99999 : R := 99999 / 100000.

Example truncate_test : truncate_number_spec R999_99999 R0_99999.
Proof.
  unfold truncate_number_spec, R999_99999, R0_99999.
  split.
  - lra.
  - exists 999%Z.
    split.
    + simpl.
      split; lra.
    + split.
      * simpl. lra.
      * lra.
Qed.