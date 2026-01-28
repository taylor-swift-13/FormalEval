Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.

Open Scope Z_scope.

Definition largest_divisor_spec (n res : Z) : Prop :=
  Z.divide res n /\
  ((n <= 1 /\ res = 1) \/
   (n >= 2 /\ 1 <= res < n /\
    (forall m : Z, 1 <= m < n -> Z.divide m n -> m <= res))).

Example test_case_2 : largest_divisor_spec 30 15.
Proof.
  unfold largest_divisor_spec.
  split.
  - (* Prove 15 divides 30 *)
    exists 2. reflexivity.
  - (* Prove constraints for n = 30 *)
    right.
    split.
    + lia. (* 30 >= 2 *)
    + split.
      * lia. (* 1 <= 15 < 30 *)
      * intros m H_range H_div.
        destruct H_div as [k Hk].
        (* 30 = k * m *)
        assert (H_eq: 30 = k * m) by lia.
        (* Since m < 30 and m >= 1, k must be >= 2 *)
        assert (H_k: k >= 2).
        {
          destruct (Z.le_gt_cases k 1).
          - (* k <= 1 implies k * m <= m < 30 *)
            assert (k * m <= 1 * m).
            { apply Z.mul_le_mono_nonneg_r; lia. }
            lia.
          - lia.
        }
        (* 2 * m <= k * m = 30 implies m <= 15 *)
        assert (2 * m <= 30).
        { rewrite H_eq. apply Z.mul_le_mono_nonneg_r; lia. }
        lia.
Qed.