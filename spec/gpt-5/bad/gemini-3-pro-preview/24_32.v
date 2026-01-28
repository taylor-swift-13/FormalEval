Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.

Open Scope Z_scope.

Definition largest_divisor_spec (n res : Z) : Prop :=
  Z.divide res n /\
  ((n <= 1 /\ res = 1) \/
   (n >= 2 /\ 1 <= res < n /\
    (forall m : Z, 1 <= m < n -> Z.divide m n -> m <= res))).

Example test_case_1 : largest_divisor_spec 28 14.
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
        assert (H_eq : k * m = 28). { rewrite Hk. reflexivity. }
        assert (H_k_pos : k > 0).
        {
          destruct (Z.le_gt_dec k 0); try assumption.
          assert (H_neg : k * m <= 0).
          { apply Z.mul_nonpos_nonneg; lia. }
          lia.
        }
        assert (H_k_gt_1 : k > 1).
        {
          destruct (Z.eq_dec k 1).
          - subst. lia.
          - lia.
        }
        assert (H_k_ge_2 : k >= 2) by lia.
        assert (H_le : 2 * m <= 28).
        {
          rewrite <- H_eq.
          apply Z.mul_le_mono_nonneg_r; lia.
        }
        lia.
Qed.