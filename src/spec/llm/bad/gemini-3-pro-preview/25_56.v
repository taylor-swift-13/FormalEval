Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (p : Z) : Prop :=
  p > 1 /\ forall d : Z, 0 <= d -> (d | p) -> d = 1 \/ d = p.

Definition factorize_spec (n : Z) (factors : list Z) : Prop :=
  fold_right Z.mul 1 factors = n /\
  Forall is_prime factors /\
  Sorted Z.le factors.

Lemma is_prime_equiv : forall p, is_prime p <-> prime p.
Proof.
  intros p. split.
  - intros [Hgt Hforall]. split; auto.
    intros n Hrange Hdiv.
    assert (0 <= n) by lia.
    specialize (Hforall n H Hdiv).
    lia.
  - intros [Hgt Hprime]. split; auto.
    intros d Hpos Hdiv.
    destruct (Z.eq_dec d 1); auto.
    destruct (Z.eq_dec d p); auto.
    assert (d <> 0). { intro; subst. apply Z.divide_0_l in Hdiv. subst. lia. }
    assert (1 < d < p).
    { split.
      - lia.
      - apply Z.divide_pos_le in Hdiv; lia. }
    exfalso. apply (Hprime d); auto.
Qed.

Example test_factorize_large : factorize_spec 2147483646 [2; 3; 3; 7; 11; 31; 151; 331].
Proof.
  unfold factorize_spec.
  split.
  - reflexivity.
  - split.
    + repeat (constructor; try (apply is_prime_equiv; match goal with |- prime ?p => destruct (prime_dec p); [assumption|contradiction] end)).
    + repeat constructor; simpl; try lia.
Qed.