Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.

Open Scope Z_scope.

Definition largest_divisor_spec (n res : Z) : Prop :=
  Z.divide res n /\
  ((n <= 1 /\ res = 1) \/
   (n >= 2 /\ 1 <= res < n /\
    (forall m : Z, 1 <= m < n -> Z.divide m n -> m <= res))).

Example test_largest_divisor_3 : largest_divisor_spec 3 1.
Proof.
  unfold largest_divisor_spec.
  split.
  - (* 1 divides 3 *)
    exists 3. lia.
  - (* Second part: n >= 2 case *)
    right.
    split.
    + lia.
    + split.
      * lia.
      * intros m Hm Hdiv.
        (* m divides 3, and 1 <= m < 3, so m can only be 1 *)
        destruct Hdiv as [k Hk].
        assert (Hm_pos: m > 0) by lia.
        assert (Hk_pos: k > 0).
        {
          destruct (Z.lt_trichotomy k 0) as [Hk_neg | [Hk_zero | Hk_pos]].
          - (* k < 0 *)
            assert (3 = k * m) by lia.
            assert (k * m < 0) by nia.
            lia.
          - (* k = 0 *)
            subst k. simpl in Hk. lia.
          - (* k > 0 *)
            lia.
        }
        assert (Hm_bound: m < 3) by lia.
        assert (Hm_ge1: m >= 1) by lia.
        (* Since m divides 3 and 1 <= m < 3, m must be 1 *)
        assert (Hm_cases: m = 1 \/ m = 2) by lia.
        destruct Hm_cases as [Hm1 | Hm2].
        -- lia.
        -- (* m = 2, but 2 does not divide 3 *)
           subst m.
           assert (H3eq: 3 = k * 2) by lia.
           (* 3 = 2 * k means k = 3/2, which is not an integer *)
           destruct (Z.eq_dec k 1) as [Hk1 | Hk_not1].
           ++ subst k. lia.
           ++ assert (k >= 2) by lia.
              assert (k * 2 >= 4) by lia.
              lia.
Qed.