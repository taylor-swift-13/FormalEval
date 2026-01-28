Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.

Open Scope Z_scope.

Definition largest_divisor_spec (n res : Z) : Prop :=
  Z.divide res n /\
  ((n <= 1 /\ res = 1) \/
   (n >= 2 /\ 1 <= res < n /\
    (forall m : Z, 1 <= m < n -> Z.divide m n -> m <= res))).

Example test_case_1 : largest_divisor_spec 76 38.
Proof.
  unfold largest_divisor_spec.
  split.
  - exists 2. reflexivity.
  - right.
    split.
    + lia.
    + split.
      * lia.
      * intros m H_range H_div.
        destruct H_div as [k Hk].
        assert (H_eq: k * m = 76) by lia.
        assert (Hm_pos: m > 0) by lia.
        assert (Hk_pos: k > 0).
        {
          destruct (Z_le_gt_dec k 0).
          - assert (k * m <= 0).
            { apply Z.mul_nonpos_nonneg; lia. }
            lia.
          - assumption.
        }
        assert (Hk_gt_1: k > 1).
        {
          destruct (Z_le_gt_dec k 1).
          - assert (k = 1) by lia.
            subst.
            lia.
          - assumption.
        }
        assert (Hk_ge_2: k >= 2) by lia.
        assert (H_ineq: 2 * m <= k * m).
        { apply Z.mul_le_mono_nonneg_r; lia. }
        rewrite H_eq in H_ineq.
        lia.
Qed.