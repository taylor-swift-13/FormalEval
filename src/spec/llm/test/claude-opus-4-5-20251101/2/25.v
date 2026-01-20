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

Definition R_input : R := 984438743601213 / 1000000000000000.
Definition R_output : R := 984438743601213 / 1000000000000000.

Example truncate_test : truncate_number_spec R_input R_output.
Proof.
  unfold truncate_number_spec, R_input, R_output.
  split.
  - cut (0 < 984438743601213 / 1000000000000000).
    + lra.
    + apply Rdiv_lt_0_compat; lra.
  - exists 0%Z.
    split.
    + simpl.
      split.
      * lra.
      * apply Rmult_lt_reg_r with 1000000000000000.
        -- lra.
        -- unfold Rdiv.
           rewrite Rmult_assoc.
           rewrite Rinv_l.
           ++ lra.
           ++ lra.
    + split.
      * simpl. lra.
      * split.
        -- apply Rmult_le_reg_r with 1000000000000000.
           ++ lra.
           ++ unfold Rdiv.
              rewrite Rmult_0_l.
              rewrite Rmult_assoc.
              rewrite Rinv_l.
              ** lra.
              ** lra.
        -- apply Rmult_lt_reg_r with 1000000000000000.
           ++ lra.
           ++ unfold Rdiv.
              rewrite Rmult_assoc.
              rewrite Rinv_l.
              ** lra.
              ** lra.
Qed.