Require Import Reals.
Require Import Floats.
Require Import ZArith.
Require Import Lia.
Require Import Psatz.

Open Scope R_scope.

Definition truncate_number_spec (number : R) (result : R) : Prop :=
  number > 0 /\
  exists (int_part : Z), 
    IZR int_part <= number < IZR (int_part + 1) /\
    result = number - IZR int_part /\
    0 <= result < 1.

Example truncate_number_spec_test : truncate_number_spec 3.5%R 0.5%R.
Proof.
  unfold truncate_number_spec.
  split.
  - lra.
  - exists 3%Z.
    split.
    + replace (3 + 1)%Z with 4%Z by lia.
      change (IZR 3%Z) with 3%R.
      change (IZR 4%Z) with 4%R.
      split; lra.
    + split.
      * change (IZR 3%Z) with 3%R. lra.
      * lra.
Qed.