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

Lemma is_prime_3 : is_prime 3.
Proof.
  unfold is_prime.
  split.
  - lia.
  - intros d Hd.
    assert (d = 2) as Hcase by lia.
    subst d. compute. discriminate.
Qed.

Lemma is_factor_3_27 : is_factor 3 27.
Proof.
  unfold is_factor.
  compute. reflexivity.
Qed.

Lemma not_prime_27 : ~(is_prime 27).
Proof.
  unfold is_prime.
  intros [H1 H2].
  specialize (H2 3).
  assert (1 < 3 < 27) as H3 by lia.
  specialize (H2 H3).
  compute in H2.
  contradiction.
Qed.

Lemma prime_factor_bound_27 : forall f : Z, is_prime_factor f 27 -> f <= 3.
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
                     +++ subst f.
                         exfalso.
                         specialize (Hdiv 3).
                         assert (1 < 3 < 9) as H3 by lia.
                         specialize (Hdiv H3).
                         compute in Hdiv.
                         contradiction.
                     +++ destruct (Z.eq_dec f 10).
                         *** subst. compute in Hfactor. discriminate.
                         *** destruct (Z.eq_dec f 11).
                             ---- subst. compute in Hfactor. discriminate.
                             ---- destruct (Z.eq_dec f 12).
                                  ++++ subst. compute in Hfactor. discriminate.
                                  ++++ destruct (Z.eq_dec f 13).
                                       **** subst. compute in Hfactor. discriminate.
                                       **** destruct (Z.eq_dec f 14).
                                            ----- subst. compute in Hfactor. discriminate.
                                            ----- destruct (Z.eq_dec f 15).
                                                  +++++ subst. compute in Hfactor. discriminate.
                                                  +++++ destruct (Z.eq_dec f 16).
                                                        ***** subst. compute in Hfactor. discriminate.
                                                        ***** destruct (Z.eq_dec f 17).
                                                              { subst. compute in Hfactor. discriminate. }
                                                              { destruct (Z.eq_dec f 18).
                                                                { subst. compute in Hfactor. discriminate. }
                                                                { destruct (Z.eq_dec f 19).
                                                                  { subst. compute in Hfactor. discriminate. }
                                                                  { destruct (Z.eq_dec f 20).
                                                                    { subst. compute in Hfactor. discriminate. }
                                                                    { destruct (Z.eq_dec f 21).
                                                                      { subst. compute in Hfactor. discriminate. }
                                                                      { destruct (Z.eq_dec f 22).
                                                                        { subst. compute in Hfactor. discriminate. }
                                                                        { destruct (Z.eq_dec f 23).
                                                                          { subst. compute in Hfactor. discriminate. }
                                                                          { destruct (Z.eq_dec f 24).
                                                                            { subst. compute in Hfactor. discriminate. }
                                                                            { destruct (Z.eq_dec f 25).
                                                                              { subst. compute in Hfactor. discriminate. }
                                                                              { destruct (Z.eq_dec f 26).
                                                                                { subst. compute in Hfactor. discriminate. }
                                                                                { destruct (Z.eq_dec f 27).
                                                                                  { subst f.
                                                                                    exfalso.
                                                                                    specialize (Hdiv 3).
                                                                                    assert (1 < 3 < 27) as H3 by lia.
                                                                                    specialize (Hdiv H3).
                                                                                    compute in Hdiv.
                                                                                    contradiction. }
                                                                                  { destruct (Z.le_gt_cases f 27).
                                                                                    { lia. }
                                                                                    { assert (Z.rem 27 f = 27).
                                                                                      { apply Z.rem_small. lia. }
                                                                                      rewrite H0 in Hfactor.
                                                                                      discriminate. } } } } } } } } } } } } } }
Qed.

Example largest_prime_factor_27 : largest_prime_factor_spec 27 3.
Proof.
  unfold largest_prime_factor_spec.
  split.
  - lia.
  - split.
    + exact not_prime_27.
    + split.
      * unfold is_prime_factor.
        split.
        -- exact is_prime_3.
        -- exact is_factor_3_27.
      * exact prime_factor_bound_27.
Qed.