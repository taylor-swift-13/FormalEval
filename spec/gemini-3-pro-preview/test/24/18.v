Require Import Coq.ZArith.ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition largest_divisor_spec (n : Z) (result : Z) : Prop :=
  Z.divide result n /\
  result < n /\
  (forall k : Z, Z.divide k n -> k < n -> k <= result).

Example test_largest_divisor_73: largest_divisor_spec 73 1.
Proof.
  unfold largest_divisor_spec.
  split.
  - exists 73. reflexivity.
  - split.
    + lia.
    + intros k [x Hx] Hlt.
      destruct (Z_le_gt_dec k 1).
      * assumption.
      * assert (x > 1).
        { destruct (Z_le_gt_dec x 1); try lia.
          assert (x * k <= 1 * k) by (apply Z.mul_le_mono_nonneg_r; lia).
          lia. }
        assert (x <= 8 \/ k <= 8).
        { destruct (Z_le_gt_dec x 8); [left|destruct (Z_le_gt_dec k 8); [right|]]; try assumption.
          assert (x >= 9 /\ k >= 9) by lia. nia. }
        destruct H0 as [Hsmall|Hsmall].
        -- assert (Hdiv: Z.divide x 73) by (exists k; lia).
           assert (x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7 \/ x = 8) by lia.
           destruct H0 as [?|[?|[?|[?|[?|[?|?]]]]]]; subst;
             apply Z.mod_divide in Hdiv; try lia; simpl in Hdiv; discriminate.
        -- assert (Hdiv: Z.divide k 73) by (exists x; lia).
           assert (k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8) by lia.
           destruct H0 as [?|[?|[?|[?|[?|[?|?]]]]]]; subst;
             apply Z.mod_divide in Hdiv; try lia; simpl in Hdiv; discriminate.
Qed.