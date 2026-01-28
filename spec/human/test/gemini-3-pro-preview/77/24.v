Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_77_pre (a : Z) : Prop := True.

Definition problem_77_spec (a : Z) (b : bool) : Prop :=
  (b = true <-> (exists x : Z, a = x * x * x)).

Example test_iscube_2 : problem_77_spec 999999 false.
Proof.
  unfold problem_77_spec.
  split.
  - intros H. discriminate H.
  - intros [x H].
    assert (H_dec : x < 100 \/ x >= 100) by lia.
    destruct H_dec as [H_lt | H_ge].
    + assert (H_le : x <= 99) by lia.
      destruct (Z_lt_ge_dec x 0) as [H_neg | H_nonneg].
      * assert (H_cube : x * x * x < 0).
        { apply Z.mul_pos_neg.
          - apply Z.mul_neg_neg; lia.
          - lia. }
        lia.
      * assert (H_sq : x * x <= 99 * 99).
        { apply Z.mul_le_mono_nonneg; lia. }
        assert (H_cube : x * x * x <= 99 * 99 * 99).
        { apply Z.mul_le_mono_nonneg; lia. }
        lia.
    + assert (H_sq : 100 * 100 <= x * x).
      { apply Z.mul_le_mono_nonneg; lia. }
      assert (H_cube : 100 * 100 * 100 <= x * x * x).
      { apply Z.mul_le_mono_nonneg; lia. }
      lia.
Qed.