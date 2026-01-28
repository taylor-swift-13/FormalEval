Require Import Coq.ZArith.ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition largest_divisor_spec (n : Z) (result : Z) : Prop :=
  Z.divide result n /\
  result < n /\
  (forall k : Z, Z.divide k n -> k < n -> k <= result).

Example test_largest_divisor_235: largest_divisor_spec 235 47.
Proof.
  unfold largest_divisor_spec.
  split.
  - exists 5. reflexivity.
  - split.
    + lia.
    + intros k Hdiv Hlt.
      destruct Hdiv as [x Hx].
      destruct (Z_le_gt_dec k 0) as [Hk_le_0 | Hk_gt_0].
      * lia.
      * assert (Hx_gt_1: x > 1).
        { assert (x * k > 1 * k). { rewrite <- Hx. lia. } nia. }
        assert (x >= 5).
        {
          assert (x = 2 \/ x = 3 \/ x = 4 \/ x >= 5) by lia.
          destruct H as [H2 | [H3 | [H4 | H5]]].
          - subst x.
            assert (Hmod: 235 mod 2 = 0).
            { apply Z.mod_divide; [lia |]. exists k. rewrite Hx. ring. }
            vm_compute in Hmod. discriminate.
          - subst x.
            assert (Hmod: 235 mod 3 = 0).
            { apply Z.mod_divide; [lia |]. exists k. rewrite Hx. ring. }
            vm_compute in Hmod. discriminate.
          - subst x.
            assert (Hmod: 235 mod 4 = 0).
            { apply Z.mod_divide; [lia |]. exists k. rewrite Hx. ring. }
            vm_compute in Hmod. discriminate.
          - exact H5.
        }
        assert (5 * k <= 235).
        { rewrite Hx. apply Z.mul_le_mono_nonneg_r; lia. }
        lia.
Qed.