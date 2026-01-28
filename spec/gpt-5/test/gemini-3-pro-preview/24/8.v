Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.

Open Scope Z_scope.

Definition largest_divisor_spec (n res : Z) : Prop :=
  Z.divide res n /\
  ((n <= 1 /\ res = 1) \/
   (n >= 2 /\ 1 <= res < n /\
    (forall m : Z, 1 <= m < n -> Z.divide m n -> m <= res))).

Example test_case_1 : largest_divisor_spec 101 1.
Proof.
  unfold largest_divisor_spec.
  split.
  - (* Prove 1 divides 101 *)
    exists 101. reflexivity.
  - (* Prove constraints for n = 101 *)
    right.
    split.
    + lia. (* 101 >= 2 *)
    + split.
      * lia. (* 1 <= 1 < 101 *)
      * intros m H_range H_div.
        (* We need to show that if m is a divisor of 101 in [1, 101), then m <= 1 *)
        assert (m = 1 \/ m > 1) as H_cases by lia.
        destruct H_cases as [H_eq1 | H_gt1].
        -- (* Case m = 1 *)
           subst. lia.
        -- (* Case m > 1 *)
           assert (m <= 10 \/ m >= 11) as H_split by lia.
           destruct H_split as [H_small | H_large].
           ++ (* m in [2, 10] *)
              assert (m = 2 \/ m = 3 \/ m = 4 \/ m = 5 \/ m = 6 \/ m = 7 \/ m = 8 \/ m = 9 \/ m = 10) as H_vals by lia.
              repeat (destruct H_vals as [H_val | H_vals]; [
                subst; apply Z.mod_divide in H_div; [vm_compute in H_div; discriminate | lia]
              | ]).
              subst; apply Z.mod_divide in H_div; [vm_compute in H_div; discriminate | lia].
           ++ (* m >= 11 *)
              destruct H_div as [k Hk].
              (* 101 = k * m. Since m >= 11, k <= 9 *)
              assert (k * 11 <= k * m) by (apply Z.mul_le_mono_nonneg_l; lia).
              rewrite <- Hk in H.
              assert (k <= 9) by lia.
              
              (* Also k is a divisor of 101 *)
              assert (Z.divide k 101) as H_k_div.
              { exists m. rewrite Z.mul_comm. exact Hk. }
              
              (* k cannot be 1 because m would be 101, but m < 101 *)
              assert (k <> 1).
              { intro. subst. rewrite Z.mul_1_l in Hk. subst. lia. }
              
              (* k cannot be 0 *)
              assert (k <> 0).
              { intro. subst. rewrite Z.mul_0_l in Hk. discriminate. }
              
              assert (k >= 2) by lia.
              
              (* So k is in [2, 9] *)
              assert (k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9) as H_k_vals by lia.
              repeat (destruct H_k_vals as [H_val | H_k_vals]; [
                subst; apply Z.mod_divide in H_k_div; [vm_compute in H_k_div; discriminate | lia]
              | ]).
              subst; apply Z.mod_divide in H_k_div; [vm_compute in H_k_div; discriminate | lia].
Qed.