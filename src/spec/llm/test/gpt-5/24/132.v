Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition largest_divisor_spec (n res : Z) : Prop :=
  Z.divide res n /\
  ((n <= 1 /\ res = 1) \/
   (n >= 2 /\ 1 <= res < n /\
    (forall m : Z, 1 <= m < n -> Z.divide m n -> m <= res))).

Example largest_divisor_spec_131 : largest_divisor_spec 131%Z 1%Z.
Proof.
  unfold largest_divisor_spec.
  split.
  - exists 131%Z. lia.
  - right.
    split; [lia|].
    split; [lia|].
    intros m Hm Hdiv.
    destruct Hm as [Hm1 Hm2].
    destruct Hdiv as [k Hk].
    destruct (Z_lt_ge_dec m 2) as [Hm_lt2 | Hm_ge2].
    + assert (m = 1%Z) by lia. subst m. lia.
    + assert (k <= 0 \/ 1 <= k) by lia.
      destruct H as [Hk_le0 | Hk_ge1].
      * assert (m*k <= 0) by lia. lia.
      * destruct (Z_lt_ge_dec k 2) as [Hk_lt2 | Hk_ge2].
        -- assert (k = 1%Z) by lia. subst k. exfalso. lia.
        -- destruct (Z_le_gt_dec m 11) as [Hm_le11 | Hm_gt11].
           ++ destruct (Z_le_gt_dec m 2) as [Hm_le2 | Hm_gt2].
              ** assert (m = 2%Z) by lia. subst m.
                 assert (k <= 65 \/ 66 <= k) by lia.
                 destruct H as [Hk_le65 | Hk_ge66]; exfalso; lia.
              ** destruct (Z_le_gt_dec m 3) as [Hm_le3 | Hm_gt3].
                 --- assert (m = 3%Z) by lia. subst m.
                     assert (k <= 43 \/ 44 <= k) by lia.
                     destruct H as [Hk_le43 | Hk_ge44]; exfalso; lia.
                 --- destruct (Z_le_gt_dec m 4) as [Hm_le4 | Hm_gt4].
                     +++ assert (m = 4%Z) by lia. subst m.
                         assert (k <= 32 \/ 33 <= k) by lia.
                         destruct H as [Hk_le32 | Hk_ge33]; exfalso; lia.
                     +++ destruct (Z_le_gt_dec m 5) as [Hm_le5 | Hm_gt5].
                         *** assert (m = 5%Z) by lia. subst m.
                             assert (k <= 26 \/ 27 <= k) by lia.
                             destruct H as [Hk_le26 | Hk_ge27]; exfalso; lia.
                         *** destruct (Z_le_gt_dec m 6) as [Hm_le6 | Hm_gt6].
                             ---- assert (m = 6%Z) by lia. subst m.
                                  assert (k <= 21 \/ 22 <= k) by lia.
                                  destruct H as [Hk_le21 | Hk_ge22]; exfalso; lia.
                             ---- destruct (Z_le_gt_dec m 7) as [Hm_le7 | Hm_gt7].
                                  ***** assert (m = 7%Z) by lia. subst m.
                                        assert (k <= 18 \/ 19 <= k) by lia.
                                        destruct H as [Hk_le18 | Hk_ge19]; exfalso; lia.
                                  ***** destruct (Z_le_gt_dec m 8) as [Hm_le8 | Hm_gt8].
                                        +++++ assert (m = 8%Z) by lia. subst m.
                                              assert (k <= 16 \/ 17 <= k) by lia.
                                              destruct H as [Hk_le16 | Hk_ge17]; exfalso; lia.
                                        +++++ destruct (Z_le_gt_dec m 9) as [Hm_le9 | Hm_gt9].
                                              ****** assert (m = 9%Z) by lia. subst m.
                                                     assert (k <= 14 \/ 15 <= k) by lia.
                                                     destruct H as [Hk_le14 | Hk_ge15]; exfalso; lia.
                                              ****** destruct (Z_le_gt_dec m 10) as [Hm_le10 | Hm_gt10].
                                                     ------- assert (m = 10%Z) by lia. subst m.
                                                             assert (k <= 13 \/ 14 <= k) by lia.
                                                             destruct H as [Hk_le13 | Hk_ge14]; exfalso; lia.
                                                     ------- assert (m = 11%Z) by lia. subst m.
                                                             assert (k <= 11 \/ 12 <= k) by lia.
                                                             destruct H as [Hk_le11k | Hk_ge12]; exfalso; lia.
           ++ assert (k <= 10 \/ 11 <= k) by lia.
              destruct H as [Hk_le10 | Hk_ge11].
              ** destruct (Z_le_gt_dec k 2) as [Hk_le2 | Hk_gt2].
                 --- assert (k = 2%Z) by lia. subst k.
                     assert (m <= 65 \/ 66 <= m) by lia.
                     destruct H as [Hm_le65 | Hm_ge66]; exfalso; lia.
                 --- destruct (Z_le_gt_dec k 3) as [Hk_le3 | Hk_gt3].
                     +++ assert (k = 3%Z) by lia. subst k.
                         assert (m <= 43 \/ 44 <= m) by lia.
                         destruct H as [Hm_le43 | Hm_ge44]; exfalso; lia.
                     +++ destruct (Z_le_gt_dec k 4) as [Hk_le4 | Hk_gt4].
                         *** assert (k = 4%Z) by lia. subst k.
                             assert (m <= 32 \/ 33 <= m) by lia.
                             destruct H as [Hm_le32 | Hm_ge33]; exfalso; lia.
                         *** destruct (Z_le_gt_dec k 5) as [Hk_le5 | Hk_gt5].
                             ---- assert (k = 5%Z) by lia. subst k.
                                  assert (m <= 26 \/ 27 <= m) by lia.
                                  destruct H as [Hm_le26 | Hm_ge27]; exfalso; lia.
                             ---- destruct (Z_le_gt_dec k 6) as [Hk_le6 | Hk_gt6].
                                  ***** assert (k = 6%Z) by lia. subst k.
                                        assert (m <= 21 \/ 22 <= m) by lia.
                                        destruct H as [Hm_le21 | Hm_ge22]; exfalso; lia.
                                  ***** destruct (Z_le_gt_dec k 7) as [Hk_le7 | Hk_gt7].
                                        +++++ assert (k = 7%Z) by lia. subst k.
                                              assert (m <= 18 \/ 19 <= m) by lia.
                                              destruct H as [Hm_le18 | Hm_ge19]; exfalso; lia.
                                        +++++ destruct (Z_le_gt_dec k 8) as [Hk_le8 | Hk_gt8].
                                              ****** assert (k = 8%Z) by lia. subst k.
                                                     assert (m <= 16 \/ 17 <= m) by lia.
                                                     destruct H as [Hm_le16 | Hm_ge17]; exfalso; lia.
                                              ****** destruct (Z_le_gt_dec k 9) as [Hk_le9 | Hk_gt9].
                                                     ------- assert (k = 9%Z) by lia. subst k.
                                                             assert (m <= 14 \/ 15 <= m) by lia.
                                                             destruct H as [Hm_le14 | Hm_ge15]; exfalso; lia.
                                                     ------- assert (k = 10%Z) by lia. subst k.
                                                             assert (m <= 13 \/ 14 <= m) by lia.
                                                             destruct H as [Hm_le13 | Hm_ge14]; exfalso; lia.
              ** exfalso. lia.
Qed.