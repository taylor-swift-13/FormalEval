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

Example test_largest_divisor_236 : largest_divisor_spec 236 118.
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
           assert (Hd_range: 119 <= d <= 235) by lia.
           destruct (Z.eq_dec (236 mod d) 0) as [Hdiv | Hndiv].
           ++ assert (d = 118 \/ d = 236 \/ (236 mod d <> 0)).
              { destruct (Z.eq_dec d 118); [left; auto |].
                destruct (Z.eq_dec d 236); [right; left; auto |].
                right; right.
                assert (Hpos: d > 0) by lia.
                assert (H236pos: 236 > 0) by lia.
                assert (Hquot: 236 / d = 1 \/ 236 / d = 2).
                { assert (236 / d >= 1).
                  { apply Z.div_le_lower_bound; lia. }
                  assert (236 / d <= 1).
                  { apply Z.div_le_upper_bound; lia. }
                  lia. }
                destruct Hquot as [Hq1 | Hq2].
                - assert (236 = d * 1 + 236 mod d).
                  { rewrite <- Hq1. apply Z.div_mod. lia. }
                  assert (236 mod d >= 0) by (apply Z.mod_pos_bound; lia).
                  assert (236 mod d < d) by (apply Z.mod_pos_bound; lia).
                  lia.
                - assert (236 = d * 2 + 236 mod d).
                  { rewrite <- Hq2. apply Z.div_mod. lia. }
                  assert (236 mod d >= 0) by (apply Z.mod_pos_bound; lia).
                  assert (236 mod d < d) by (apply Z.mod_pos_bound; lia).
                  lia. }
              destruct H0 as [Heq118 | [Heq236 | Hmod_ne]].
              ** lia.
              ** lia.
              ** exact Hmod_ne.
           ++ exact Hndiv.
Qed.