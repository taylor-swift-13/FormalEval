Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.

Open Scope Z_scope.

Definition largest_divisor_spec (n res : Z) : Prop :=
  Z.divide res n /\
  ((n <= 1 /\ res = 1) \/
   (n >= 2 /\ 1 <= res < n /\
    (forall m : Z, 1 <= m < n -> Z.divide m n -> m <= res))).

Example test_case_1 : largest_divisor_spec 235 47.
Proof.
  unfold largest_divisor_spec.
  split.
  - (* Prove 47 divides 235 *)
    exists 5. reflexivity.
  - (* Prove constraints for n = 235 *)
    right.
    split.
    + lia. (* 235 >= 2 *)
    + split.
      * lia. (* 1 <= 47 < 235 *)
      * intros m H_range H_div.
        destruct H_div as [k Hk].
        (* We have 235 = k * m *)
        (* Since m < 235 and m >= 1, k must be > 1 *)
        assert (k > 1).
        {
          destruct (Z_le_gt_dec k 1); [| assumption].
          assert (k * m <= 1 * m) by (apply Z.mul_le_mono_nonneg_r; lia).
          lia.
        }
        (* Check that k cannot be 2, 3, 4 *)
        assert (H_div_k: Z.divide k 235).
        { exists m. rewrite Z.mul_comm. assumption. }
        apply Z.mod_divide in H_div_k; [| lia].
        
        assert (k <> 2) by (intro; subst; vm_compute in H_div_k; discriminate).
        assert (k <> 3) by (intro; subst; vm_compute in H_div_k; discriminate).
        assert (k <> 4) by (intro; subst; vm_compute in H_div_k; discriminate).
        
        assert (k >= 5) by lia.
        
        (* Now derive m <= 47 *)
        (* 235 = k * m >= 5 * m *)
        assert (5 * m <= 235).
        { rewrite Hk. apply Z.mul_le_mono_nonneg_r; lia. }
        (* 5 * m <= 235 implies m <= 47 *)
        lia.
Qed.