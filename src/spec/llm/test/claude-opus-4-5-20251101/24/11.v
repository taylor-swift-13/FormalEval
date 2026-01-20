Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition largest_divisor_spec (n : Z) (result : Z) : Prop :=
  (n <= 1 -> result = 1) /\
  (n > 1 -> 
    result >= 1 /\
    result < n /\
    (n mod result = 0) /\
    (forall d : Z, d > result -> d < n -> n mod d <> 0 \/ d * (n / d) <> n / (n / d))).

Example test_largest_divisor_999 : largest_divisor_spec 999 333.
Proof.
  unfold largest_divisor_spec.
  split.
  - intro H. lia.
  - intro H.
    split.
    + lia.
    + split.
      * lia.
      * split.
        -- compute. reflexivity.
        -- intros d Hd1 Hd2.
           left.
           assert (Hd_range: 333 < d < 999) by lia.
           assert (H999_div: forall x, 333 < x < 999 -> x <> 499 -> 999 mod x <> 0).
           {
             intros x Hx Hneq.
             destruct (Z.eq_dec x 334); [subst; compute; discriminate|].
             destruct (Z.eq_dec x 335); [subst; compute; discriminate|].
             destruct (Z.eq_dec x 336); [subst; compute; discriminate|].
             destruct (Z.eq_dec x 337); [subst; compute; discriminate|].
             destruct (Z.eq_dec x 338); [subst; compute; discriminate|].
             destruct (Z.eq_dec x 339); [subst; compute; discriminate|].
             destruct (Z.eq_dec x 340); [subst; compute; discriminate|].
             destruct (Z.eq_dec x 499); [contradiction|].
             destruct (Z.eq_dec x 500); [subst; compute; discriminate|].
             assert (Hdiv: 999 = 3 * 333) by lia.
             intro Hmod.
             apply Z.mod_divide in Hmod; [|lia].
             destruct Hmod as [k Hk].
             assert (Hk_bounds: k >= 1 /\ k <= 2).
             {
               split.
               - destruct (Z_lt_dec k 1); [|lia].
                 assert (k <= 0) by lia.
                 destruct (Z.eq_dec k 0); [subst; lia|].
                 assert (k < 0) by lia.
                 assert (x * k < 0) by (apply Z.mul_neg_pos; lia).
                 lia.
               - destruct (Z_lt_dec 2 k); [|lia].
                 assert (k >= 3) by lia.
                 assert (x * k >= 334 * 3) by nia.
                 lia.
             }
             destruct Hk_bounds as [Hk1 Hk2].
             assert (k = 1 \/ k = 2) by lia.
             destruct H0.
             + subst k. lia.
             + subst k. 
               assert (x = 499) by lia.
               subst x. 
               compute in Hneq. contradiction.
           }
           destruct (Z.eq_dec d 499).
           ++ subst d. compute. discriminate.
           ++ apply H999_div; lia.
Qed.