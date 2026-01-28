Require Import Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.
Open Scope Z_scope.

Definition problem_75_pre (a : Z) : Prop := a < 100.

Definition problem_75_spec (a : Z) (b : bool) : Prop :=
  (b = true <-> exists p1 p2 p3, prime p1 /\ prime p2 /\ prime p3 /\ a = p1 * p2 * p3).

Example problem_75_test_5 : problem_75_pre 5%Z /\ problem_75_spec 5%Z false.
Proof.
  split.
  - unfold problem_75_pre; lia.
  - unfold problem_75_spec; split.
    + intros H; exfalso; discriminate H.
    + intros (p1 & p2 & p3 & Hp1 & Hp2 & Hp3 & Heq).
      assert (Hp1_ge2 : 2 <= p1) by (apply prime_ge_2; exact Hp1).
      assert (Hp2_ge2 : 2 <= p2) by (apply prime_ge_2; exact Hp2).
      assert (Hp3_ge2 : 2 <= p3) by (apply prime_ge_2; exact Hp3).
      assert (Hp1_nonneg : 0 <= p1) by lia.
      assert (Hp2_nonneg : 0 <= p2) by lia.
      assert (Hp3_nonneg : 0 <= p3) by lia.
      assert (H4_le_p1p2 : 4 <= p1 * p2).
      { replace 4 with (2 * 2)%Z by lia.
        eapply Z.le_trans.
        - apply Z.mul_le_mono_nonneg_r; [lia | exact Hp1_ge2].
        - apply Z.mul_le_mono_nonneg_l; [exact Hp1_nonneg | exact Hp2_ge2]. }
      assert (H8_le_p1p2_2 : 8 <= (p1 * p2) * 2).
      { replace 8 with (4 * 2)%Z by lia.
        apply Z.mul_le_mono_nonneg_r; [lia | exact H4_le_p1p2]. }
      assert (Hp1p2_nonneg : 0 <= p1 * p2).
      { apply Z.mul_nonneg_nonneg; [exact Hp1_nonneg | exact Hp2_nonneg]. }
      assert (H_p1p2_2_le_p1p2p3 : (p1 * p2) * 2 <= (p1 * p2) * p3).
      { apply Z.mul_le_mono_nonneg_l; [exact Hp1p2_nonneg | exact Hp3_ge2]. }
      assert (H8_le_prod : 8 <= (p1 * p2) * p3).
      { eapply Z.le_trans; [exact H8_le_p1p2_2 | exact H_p1p2_2_le_p1p2p3]. }
      rewrite Heq in H8_le_prod.
      lia.
Qed.