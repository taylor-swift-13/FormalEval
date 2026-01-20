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

Definition R3_1842364304976463 : R := 3 + 1842364304976463 / 10000000000000000.
Definition R0_18423643049764626 : R := 1842364304976463 / 10000000000000000.

Example truncate_test : truncate_number_spec R3_1842364304976463 R0_18423643049764626.
Proof.
  unfold truncate_number_spec, R3_1842364304976463, R0_18423643049764626.
  split.
  - lra.
  - exists 3%Z.
    split.
    + simpl.
      split; lra.
    + split.
      * simpl. lra.
      * split.
        -- lra.
        -- assert (H: 1842364304976463 < 10000000000000000) by lra.
           apply Rmult_lt_reg_r with (r := 10000000000000000).
           lra.
           unfold Rdiv.
           rewrite Rmult_assoc.
           rewrite Rinv_l.
           lra.
           lra.
Qed.