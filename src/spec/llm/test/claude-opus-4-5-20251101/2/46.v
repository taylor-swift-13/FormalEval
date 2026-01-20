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

Definition R2_6876956198100403 : R := 2 + 6876956198100403 / 10000000000000000.
Definition R0_6876956198100403 : R := 6876956198100403 / 10000000000000000.

Example truncate_test : truncate_number_spec R2_6876956198100403 R0_6876956198100403.
Proof.
  unfold truncate_number_spec, R2_6876956198100403, R0_6876956198100403.
  split.
  - lra.
  - exists 2%Z.
    split.
    + simpl.
      split; lra.
    + split.
      * simpl. lra.
      * lra.
Qed.