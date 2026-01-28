Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.

Open Scope Z_scope.

Definition largest_divisor_spec (n res : Z) : Prop :=
  Z.divide res n /\
  ((n <= 1 /\ res = 1) \/
   (n >= 2 /\ 1 <= res < n /\
    (forall m : Z, 1 <= m < n -> Z.divide m n -> m <= res))).

Example test_case_1 : largest_divisor_spec 35 7.
Proof.
  unfold largest_divisor_spec.
  split.
  - (* Prove 7 divides 35 *)
    exists 5. reflexivity.
  - (* Prove constraints for n = 35 *)
    right.
    split.
    + lia. (* 35 >= 2 *)
    + split.
      * lia. (* 1 <= 7 < 35 *)
      * intros m H_range H_div.
        destruct H_div as [k Hk].
        assert (Hk_eq: 35 = k * m) by lia.
        
        (* Prove k > 0 *)
        assert (k > 0).
        {
          destruct (Z_le_gt_dec k 0).
          - assert (k * m <= 0).
            { apply Z.mul_nonpos_nonneg; lia. }
            lia.
          - assumption.
        }

        (* Prove k > 1 *)
        assert (k > 1).
        {
          destruct (Z_le_gt_dec k 1).
          - assert (k = 1) by lia. subst.
            lia.
          - assumption.
        }
        
        (* k divides 35 *)
        assert (H_div_k: Z.divide k 35).
        { exists m. rewrite Z.mul_comm. assumption. }
        
        (* Check small values for k *)
        assert (k <> 2).
        { intro. subst. apply Z.mod_divide in H_div_k; [| lia]. vm_compute in H_div_k. discriminate. }
        assert (k <> 3).
        { intro. subst. apply Z.mod_divide in H_div_k; [| lia]. vm_compute in H_div_k. discriminate. }
        assert (k <> 4).
        { intro. subst. apply Z.mod_divide in H_div_k; [| lia]. vm_compute in H_div_k. discriminate. }
        
        assert (k >= 5) by lia.
        
        (* 35 = k * m >= 5 * m *)
        assert (5 * m <= 35).
        { rewrite Hk_eq. apply Z.mul_le_mono_nonneg_r; lia. }
        
        lia.
Qed.