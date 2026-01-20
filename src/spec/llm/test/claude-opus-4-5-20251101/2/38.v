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

Definition R1_8553603762907702 : R := 1 + 8553603762907702 / 10000000000000000.
Definition R0_8553603762907702 : R := 8553603762907702 / 10000000000000000.

Example truncate_test : truncate_number_spec R1_8553603762907702 R0_8553603762907702.
Proof.
  unfold truncate_number_spec, R1_8553603762907702, R0_8553603762907702.
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