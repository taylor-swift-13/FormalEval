Require Import Reals.
Require Import ZArith.
Require Import Psatz. (* Required for lra tactic *)
Require Import Floats.

Open Scope R_scope.

Definition truncate_number_spec (number : R) (result : R) : Prop :=
  number > 0 /\
  exists (int_part : Z), 
    IZR int_part <= number < IZR (int_part + 1) /\
    result = number - IZR int_part /\
    0 <= result < 1.

Example test_truncate_number : truncate_number_spec (3 * / (10 ^ 323)) (3 * / (10 ^ 323)).
Proof.
  set (x := 3 * / (10 ^ 323)).
  unfold truncate_number_spec.
  split.
  - (* number > 0 *)
    unfold x.
    apply Rmult_gt_0_compat.
    + lra.
    + apply Rinv_0_lt_compat.
      apply pow_lt.
      lra.
  - (* Instantiate int_part with 0 *)
    exists 0%Z.
    repeat split.
    + (* IZR 0 <= x *)
      replace (IZR 0) with 0 by reflexivity.
      unfold x.
      apply Rlt_le.
      apply Rmult_gt_0_compat.
      * lra.
      * apply Rinv_0_lt_compat.
        apply pow_lt.
        lra.
    + (* x < IZR (0 + 1) *)
      replace (IZR (0 + 1)) with 1 by reflexivity.
      unfold x.
      apply Rmult_lt_reg_r with (r := 10 ^ 323).
      * apply pow_lt. lra.
      * rewrite Rmult_assoc.
        rewrite Rinv_l.
        -- rewrite Rmult_1_r, Rmult_1_l.
           eapply Rlt_le_trans.
           ++ apply (Rlt_trans _ 10). lra.
              apply Rle_refl.
           ++ rewrite <- (pow_1 10).
              apply pow_le.
              ** lra.
              ** lia.
        -- apply Rgt_not_eq.
           apply pow_lt.
           lra.
    + (* result = number - IZR int_part *)
      replace (IZR 0) with 0 by reflexivity.
      rewrite Rminus_0_r.
      reflexivity.
    + (* 0 <= result *)
      replace (IZR 0) with 0 in *.
      unfold x.
      apply Rlt_le.
      apply Rmult_gt_0_compat.
      * lra.
      * apply Rinv_0_lt_compat.
        apply pow_lt.
        lra.
    + (* result < 1 *)
      replace (IZR (0 + 1)) with 1 in *.
      unfold x.
      apply Rmult_lt_reg_r with (r := 10 ^ 323).
      * apply pow_lt. lra.
      * rewrite Rmult_assoc.
        rewrite Rinv_l.
        -- rewrite Rmult_1_r, Rmult_1_l.
           eapply Rlt_le_trans.
           ++ apply (Rlt_trans _ 10). lra.
              apply Rle_refl.
           ++ rewrite <- (pow_1 10).
              apply pow_le.
              ** lra.
              ** lia.
        -- apply Rgt_not_eq.
           apply pow_lt.
           lra.
Qed.