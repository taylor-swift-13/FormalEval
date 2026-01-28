Require Import Coq.ZArith.ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition largest_divisor_spec (n : Z) (result : Z) : Prop :=
  Z.divide result n /\
  result < n /\
  (forall k : Z, Z.divide k n -> k < n -> k <= result).

Example test_largest_divisor_1001: largest_divisor_spec 1001 143.
Proof.
  unfold largest_divisor_spec.
  split.
  - exists 7. reflexivity.
  - split.
    + lia.
    + intros k Hdiv Hlt.
      destruct Hdiv as [x Hx].
      assert (k <= 0 \/ k > 0) as Hk_sign by lia.
      destruct Hk_sign as [Hk_neg | Hk_pos].
      * lia.
      * assert (x > 1).
        { destruct (Z_le_gt_dec x 1); try assumption.
          assert (x * k <= 1 * k) by (apply Zmult_le_compat_r; lia).
          lia. }
        assert (Hmod: 1001 mod x = 0).
        { rewrite Hx, Z.mul_comm. apply Z.mod_mul. lia. }
        assert (x >= 7).
        {
          assert (x <> 2) by (intro; subst; simpl in Hmod; discriminate).
          assert (x <> 3) by (intro; subst; simpl in Hmod; discriminate).
          assert (x <> 4) by (intro; subst; simpl in Hmod; discriminate).
          assert (x <> 5) by (intro; subst; simpl in Hmod; discriminate).
          assert (x <> 6) by (intro; subst; simpl in Hmod; discriminate).
          lia.
        }
        nia.
Qed.