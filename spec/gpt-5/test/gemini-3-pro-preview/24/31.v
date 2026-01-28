Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.

Open Scope Z_scope.

Definition largest_divisor_spec (n res : Z) : Prop :=
  Z.divide res n /\
  ((n <= 1 /\ res = 1) \/
   (n >= 2 /\ 1 <= res < n /\
    (forall m : Z, 1 <= m < n -> Z.divide m n -> m <= res))).

Example test_case_1 : largest_divisor_spec 24 12.
Proof.
  unfold largest_divisor_spec.
  split.
  - (* Prove 12 divides 24 *)
    exists 2. reflexivity.
  - (* Prove constraints for n = 24 *)
    right.
    split.
    + lia. (* 24 >= 2 *)
    + split.
      * lia. (* 1 <= 12 < 24 *)
      * intros m H_range H_div.
        (* We need to show that if m is a divisor of 24 in [1, 24), then m <= 12 *)
        destruct H_div as [k Hk].
        (* 24 = k * m. Since m < 24 and m >= 1, k must be > 1 *)
        assert (H_eq: 24 = k * m) by apply Hk.
        assert (H_k_gt_1: k > 1).
        {
          destruct (Z_le_gt_dec k 1).
          - assert (k * m <= 1 * m).
            { apply Zmult_le_compat_r; lia. }
            lia. (* 24 <= m < 24, contradiction *)
          - assumption.
        }
        assert (H_k_ge_2: k >= 2) by lia.
        (* 24 = k * m >= 2 * m implies m <= 12 *)
        assert (2 * m <= 24).
        { rewrite H_eq. apply Zmult_le_compat_r; lia. }
        lia.
Qed.