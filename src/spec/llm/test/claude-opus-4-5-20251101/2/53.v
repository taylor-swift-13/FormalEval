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

Definition R4_216338505526772 : R := 4216338505526772 / 1000000000000000.
Definition R0_21633850552677192 : R := 21633850552677192 / 100000000000000000.

Example truncate_test : truncate_number_spec R4_216338505526772 (R4_216338505526772 - 4).
Proof.
  unfold truncate_number_spec, R4_216338505526772.
  split.
  - lra.
  - exists 4%Z.
    split.
    + simpl.
      split; lra.
    + split.
      * lra.
      * lra.
Qed.