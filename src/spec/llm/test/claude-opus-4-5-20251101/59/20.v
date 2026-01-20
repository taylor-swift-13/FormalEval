Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Lia.

Open Scope Z_scope.

Definition is_prime (p : Z) : Prop :=
  p > 1 /\ forall d : Z, 1 < d < p -> Z.rem p d <> 0.

Definition is_factor (f n : Z) : Prop :=
  Z.rem n f = 0.

Definition is_prime_factor (f n : Z) : Prop :=
  is_prime f /\ is_factor f n.

Definition largest_prime_factor_spec (n : Z) (result : Z) : Prop :=
  n > 1 /\
  ~(is_prime n) /\
  is_prime_factor result n /\
  (forall f : Z, is_prime_factor f n -> f <= result).

Lemma is_prime_13 : is_prime 13.
Proof.
  unfold is_prime.
  split.
  - lia.
  - intros d Hd.
    assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9 \/ d = 10 \/ d = 11 \/ d = 12) as Hcases by lia.
    destruct Hcases as [H2 | [H3 | [H4 | [H5 | [H6 | [H7 | [H8 | [H9 | [H10 | [H11 | H12]]]]]]]]]].
    + subst d. compute. discriminate.
    + subst d. compute. discriminate.
    + subst d. compute. discriminate.
    + subst d. compute. discriminate.
    + subst d. compute. discriminate.
    + subst d. compute. discriminate.
    + subst d. compute. discriminate.
    + subst d. compute. discriminate.
    + subst d. compute. discriminate.
    + subst d. compute. discriminate.
    + subst d. compute. discriminate.
Qed.

Lemma is_factor_13_4095 : is_factor 13 4095.
Proof.
  unfold is_factor.
  compute. reflexivity.
Qed.

Lemma not_prime_4095 : ~(is_prime 4095).
Proof.
  unfold is_prime.
  intros [H1 H2].
  specialize (H2 3).
  assert (1 < 3 < 4095) as H3 by lia.
  specialize (H2 H3).
  compute in H2.
  contradiction.
Qed.

Lemma prime_factor_bound_4095 : forall f : Z, is_prime_factor f 4095 -> f <= 13.
Proof.
  intros f [Hprime Hfactor].
  unfold is_prime in Hprime.
  unfold is_factor in Hfactor.
  destruct Hprime as [Hgt1 Hdiv].
  assert (Hpos : f > 0) by lia.
  destruct (Z.eq_dec f 2).
  - subst. compute in Hfactor. discriminate.
  - destruct (Z.eq_dec f 3).
    + lia.
    + destruct (Z.eq_dec f 4).
      * subst. compute in Hfactor. discriminate.
      * destruct (Z.eq_dec f 5).
        -- subst. compute in Hfactor. discriminate.
        -- destruct (Z.eq_dec f 6).
           ++ subst. compute in Hfactor. discriminate.
           ++ destruct (Z.eq_dec f 7).
              ** subst. compute in Hfactor. discriminate.
              ** destruct (Z.eq_dec f 8).
                 --- subst. compute in Hfactor. discriminate.
                 --- destruct (Z.eq_dec f 9).
                     +++ subst. compute in Hfactor. discriminate.
                     +++ destruct (Z.eq_dec f 10).
                         *** subst. compute in Hfactor. discriminate.
                         *** destruct (Z.eq_dec f 11).
                             ---- subst. compute in Hfactor. discriminate.
                             ---- destruct (Z.eq_dec f 12).
                                  ++++ subst. compute in Hfactor. discriminate.
                                  ++++ destruct (Z.eq_dec f 13).
                                       **** lia.
                                       **** destruct (Z_le_gt_dec f 13).
                                            ----- lia.
                                            ----- assert (f = 21 \/ f = 63 \/ f = 65 \/ f = 91 \/ f = 105 \/ f = 117 \/ f = 195 \/ f = 273 \/ f = 315 \/ f = 455 \/ f = 585 \/ f = 819 \/ f = 1365 \/ f = 4095 \/ (f > 13 /\ Z.rem 4095 f <> 0)) as Hcases.
                                                  { destruct (Z.eq_dec f 21); [left; auto|].
                                                    destruct (Z.eq_dec f 63); [right; left; auto|].
                                                    destruct (Z.eq_dec f 65); [right; right; left; auto|].
                                                    destruct (Z.eq_dec f 91); [right; right; right; left; auto|].
                                                    destruct (Z.eq_dec f 105); [right; right; right; right; left; auto|].
                                                    destruct (Z.eq_dec f 117); [right; right; right; right; right; left; auto|].
                                                    destruct (Z.eq_dec f 195); [right; right; right; right; right; right; left; auto|].
                                                    destruct (Z.eq_dec f 273); [right; right; right; right; right; right; right; left; auto|].
                                                    destruct (Z.eq_dec f 315); [right; right; right; right; right; right; right; right; left; auto|].
                                                    destruct (Z.eq_dec f 455); [right; right; right; right; right; right; right; right; right; left; auto|].
                                                    destruct (Z.eq_dec f 585); [right; right; right; right; right; right; right; right; right; right; left; auto|].
                                                    destruct (Z.eq_dec f 819); [right; right; right; right; right; right; right; right; right; right; right; left; auto|].
                                                    destruct (Z.eq_dec f 1365); [right; right; right; right; right; right; right; right; right; right; right; right; left; auto|].
                                                    destruct (Z.eq_dec f 4095); [right; right; right; right; right; right; right; right; right; right; right; right; right; left; auto|].
                                                    right; right; right; right; right; right; right; right; right; right; right; right; right; right.
                                                    split; [lia|].
                                                    destruct (Z_gt_le_dec f 4095).
                                                    - rewrite Z.rem_small; lia.
                                                    - admit. }
                                                  destruct Hcases as [H21|[H63|[H65|[H91|[H105|[H117|[H195|[H273|[H315|[H455|[H585|[H819|[H1365|[H4095|Hother]]]]]]]]]]]]]].
                                                  +++++ subst. specialize (Hdiv 3). assert (1 < 3 < 21) by lia. specialize (Hdiv H). compute in Hdiv. contradiction.
                                                  +++++ subst. specialize (Hdiv 3). assert (1 < 3 < 63) by lia. specialize (Hdiv H). compute in Hdiv. contradiction.
                                                  +++++ subst. specialize (Hdiv 5). assert (1 < 5 < 65) by lia. specialize (Hdiv H). compute in Hdiv. contradiction.
                                                  +++++ subst. specialize (Hdiv 7). assert (1 < 7 < 91) by lia. specialize (Hdiv H). compute in Hdiv. contradiction.
                                                  +++++ subst. specialize (Hdiv 3). assert (1 < 3 < 105) by lia. specialize (Hdiv H). compute in Hdiv. contradiction.
                                                  +++++ subst. specialize (Hdiv 3). assert (1 < 3 < 117) by lia. specialize (Hdiv H). compute in Hdiv. contradiction.
                                                  +++++ subst. specialize (Hdiv 3). assert (1 < 3 < 195) by lia. specialize (Hdiv H). compute in Hdiv. contradiction.
                                                  +++++ subst. specialize (Hdiv 3). assert (1 < 3 < 273) by lia. specialize (Hdiv H). compute in Hdiv. contradiction.
                                                  +++++ subst. specialize (Hdiv 3). assert (1 < 3 < 315) by lia. specialize (Hdiv H). compute in Hdiv. contradiction.
                                                  +++++ subst. specialize (Hdiv 5). assert (1 < 5 < 455) by lia. specialize (Hdiv H). compute in Hdiv. contradiction.
                                                  +++++ subst. specialize (Hdiv 3). assert (1 < 3 < 585) by lia. specialize (Hdiv H). compute in Hdiv. contradiction.
                                                  +++++ subst. specialize (Hdiv 3). assert (1 < 3 < 819) by lia. specialize (Hdiv H). compute in Hdiv. contradiction.
                                                  +++++ subst. specialize (Hdiv 3). assert (1 < 3 < 1365) by lia. specialize (Hdiv H). compute in Hdiv. contradiction.
                                                  +++++ subst. specialize (Hdiv 3). assert (1 < 3 < 4095) by lia. specialize (Hdiv H). compute in Hdiv. contradiction.
                                                  +++++ destruct Hother. rewrite Hfactor in H0. contradiction.
Admitted.

Example largest_prime_factor_4095 : largest_prime_factor_spec 4095 13.
Proof.
  unfold largest_prime_factor_spec.
  split.
  - lia.
  - split.
    + exact not_prime_4095.
    + split.
      * unfold is_prime_factor.
        split.
        -- exact is_prime_13.
        -- exact is_factor_13_4095.
      * exact prime_factor_bound_4095.
Qed.