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

Definition R0_04320870526393539 : R := 4320870526393539 / 100000000000000000.

Example truncate_test : truncate_number_spec R0_04320870526393539 R0_04320870526393539.
Proof.
  unfold truncate_number_spec, R0_04320870526393539.
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