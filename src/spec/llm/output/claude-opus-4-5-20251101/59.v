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

Lemma is_prime_5 : is_prime 5.
Proof.
  unfold is_prime.
  split.
  - lia.
  - intros d Hd.
    assert (d = 2 \/ d = 3 \/ d = 4) as Hcases by lia.
    destruct Hcases as [H2 | [H3 | H4]].
    + subst d. compute. discriminate.
    + subst d. compute. discriminate.
    + subst d. compute. discriminate.
Qed.

Lemma is_factor_5_15 : is_factor 5 15.
Proof.
  unfold is_factor.
  compute. reflexivity.
Qed.

Lemma not_prime_15 : ~(is_prime 15).
Proof.
  unfold is_prime.
  intros [H1 H2].
  specialize (H2 3).
  assert (1 < 3 < 15) as H3 by lia.
  specialize (H2 H3).
  compute in H2.
  contradiction.
Qed.

Lemma prime_factor_bound_15 : forall f : Z, is_prime_factor f 15 -> f <= 5.
Proof.
  intros f [Hprime Hfactor].
  unfold is_prime in Hprime.
  unfold is_factor in Hfactor.
  destruct Hprime as [Hgt1 Hdiv].
  assert (Hpos : f > 0) by lia.
  (* Check all possible values that could divide 15 *)
  (* f must be > 1, f must divide 15, and f must be prime *)
  (* Divisors of 15 that are > 1: 3, 5, 15 *)
  (* Prime divisors: 3, 5 *)
  destruct (Z.eq_dec f 2).
  - (* f = 2 doesn't divide 15 *)
    subst. compute in Hfactor. discriminate.
  - destruct (Z.eq_dec f 3).
    + (* f = 3 *) lia.
    + destruct (Z.eq_dec f 4).
      * (* f = 4 doesn't divide 15 *)
        subst. compute in Hfactor. discriminate.
      * destruct (Z.eq_dec f 5).
        -- (* f = 5 *) lia.
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
                                       **** subst. compute in Hfactor. discriminate.
                                       **** destruct (Z.eq_dec f 14).
                                            ----- subst. compute in Hfactor. discriminate.
                                            ----- destruct (Z.eq_dec f 15).
                                                  +++++ (* f = 15 is not prime *)
                                                        subst f.
                                                        exfalso.
                                                        specialize (Hdiv 3).
                                                        assert (1 < 3 < 15) as H3 by lia.
                                                        specialize (Hdiv H3).
                                                        compute in Hdiv.
                                                        contradiction.
                                                  +++++ (* f > 15 or f < 2 *)
                                                        destruct (Z.le_gt_cases f 15).
                                                        ***** (* f <= 15 but f is not 2..15 *)
                                                              lia.
                                                        ***** (* f > 15, so Z.rem 15 f = 15 <> 0 *)
                                                              assert (Z.rem 15 f = 15).
                                                              { apply Z.rem_small. lia. }
                                                              rewrite H0 in Hfactor.
                                                              discriminate.
Qed.

Example largest_prime_factor_15 : largest_prime_factor_spec 15 5.
Proof.
  unfold largest_prime_factor_spec.
  split.
  - lia.
  - split.
    + exact not_prime_15.
    + split.
      * unfold is_prime_factor.
        split.
        -- exact is_prime_5.
        -- exact is_factor_5_15.
      * exact prime_factor_bound_15.
Qed.