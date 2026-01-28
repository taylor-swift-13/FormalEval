Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.

Open Scope Z_scope.

Definition largest_divisor_spec (n res : Z) : Prop :=
  Z.divide res n /\
  ((n <= 1 /\ res = 1) \/
   (n >= 2 /\ 1 <= res < n /\
    (forall m : Z, 1 <= m < n -> Z.divide m n -> m <= res))).

Example test_case_1 : largest_divisor_spec 100 50.
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
        assert (H_eq: k * m = 100) by (symmetry; apply Hk).
        assert (H_k_ge_2: k >= 2).
        {
          destruct (Z.le_gt_cases k 1) as [H_le | H_gt].
          - assert (k * m <= 1 * m).
            { apply Z.mul_le_mono_nonneg_r; lia. }
            rewrite H_eq in H.
            lia.
          - lia.
        }
        assert (2 * m <= k * m).
        { apply Z.mul_le_mono_nonneg_r; lia. }
        rewrite H_eq in H.
        lia.
Qed.