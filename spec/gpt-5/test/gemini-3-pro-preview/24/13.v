Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.

Open Scope Z_scope.

Definition largest_divisor_spec (n res : Z) : Prop :=
  Z.divide res n /\
  ((n <= 1 /\ res = 1) \/
   (n >= 2 /\ 1 <= res < n /\
    (forall m : Z, 1 <= m < n -> Z.divide m n -> m <= res))).

Example test_case_1 : largest_divisor_spec 36 18.
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
        assert (Hk_eq: 36 = k * m) by apply Hk.
        assert (H_k_gt_1: k > 1).
        {
          destruct (Z_le_gt_dec k 1) as [H_le | H_gt].
          - assert (k * m <= 1 * m).
            { apply Z.mul_le_mono_nonneg_r; lia. }
            rewrite Z.mul_1_l in H.
            lia.
          - assumption.
        }
        assert (H_k_ge_2: k >= 2) by lia.
        assert (2 * m <= 36).
        {
          rewrite Hk_eq.
          apply Z.mul_le_mono_nonneg_r; lia.
        }
        lia.
Qed.