Require Import Coq.ZArith.ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition largest_divisor_spec (n : Z) (result : Z) : Prop :=
  Z.divide result n /\
  result < n /\
  (forall k : Z, Z.divide k n -> k < n -> k <= result).

Example largest_divisor_3 : largest_divisor_spec 3 1.
Proof.
  unfold largest_divisor_spec.
  split.
  - (* 1 divides 3 *)
    exists 3. lia.
  - split.
    + (* 1 < 3 *)
      lia.
    + (* forall k, k divides 3 -> k < 3 -> k <= 1 *)
      intros k Hdiv Hlt.
      destruct Hdiv as [q Hq].
      (* 3 = q * k, k < 3 *)
      assert (k <> 0) as Hk_nonzero.
      { intro Hk0. subst k. lia. }
      assert (q <> 0) as Hq_nonzero.
      { intro Hq0. subst q. lia. }
      (* From 3 = q * k, we analyze possible values *)
      (* k divides 3 means k in {-3, -1, 1, 3} *)
      (* k < 3 means k in {-3, -1, 1} *)
      (* We need k <= 1 *)
      assert (Z.abs 3 = Z.abs q * Z.abs k) as Habs_eq.
      { rewrite Hq. rewrite Z.abs_mul. reflexivity. }
      simpl in Habs_eq.
      assert (Z.abs k >= 1) as Habs_k_pos.
      { destruct k; simpl; lia. }
      assert (Z.abs q >= 1) as Habs_q_pos.
      { destruct q; simpl; lia. }
      assert (Z.abs k <= 3) as Habs_k_le.
      { nia. }
      assert (Z.abs k = 1 \/ Z.abs k = 3) as Habs_cases.
      {
        assert (3 = Z.abs q * Z.abs k) as H3 by lia.
        assert (Z.abs k = 1 \/ Z.abs k = 3 \/ (Z.abs k <> 1 /\ Z.abs k <> 3)) as Htri by lia.
        destruct Htri as [H1 | [H3' | [Hn1 Hn3]]].
        - left; exact H1.
        - right; exact H3'.
        - exfalso.
          assert (Z.abs k = 2 \/ Z.abs k > 3 \/ Z.abs k < 1) as Hother by lia.
          destruct Hother as [H2 | [Hgt | Hlt']].
          + (* Z.abs k = 2 *)
            rewrite H2 in H3.
            assert (3 = Z.abs q * 2) by lia.
            nia.
          + (* Z.abs k > 3 *)
            lia.
          + (* Z.abs k < 1 *)
            lia.
      }
      destruct Habs_cases as [Habs1 | Habs3].
      * (* Z.abs k = 1, so k = 1 or k = -1, both <= 1 *)
        destruct k; simpl in Habs1; lia.
      * (* Z.abs k = 3, so k = 3 or k = -3 *)
        destruct k; simpl in Habs3; lia.
Qed.