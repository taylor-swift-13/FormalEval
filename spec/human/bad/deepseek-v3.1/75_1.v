Require Import Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.
Open Scope Z_scope.

Definition problem_75_pre (a : Z) : Prop := a < 100.

Definition problem_75_spec (a : Z) (b : bool) : Prop :=
  (b = true <-> exists p1 p2 p3, prime p1 /\ prime p2 /\ prime p3 /\ a = p1 * p2 * p3).

Lemma prime_2: prime 2.
Proof.
  constructor.
  - lia.
  - intros n Hdiv.
    assert (1 < n < 2 \/ n = 1 \/ n = 2) as [H|[H|H]].
    + destruct (Z_lt_ge_dec n 2) as [Hlt|Hge].
      * destruct (Z_lt_ge_dec 1 n) as [Hlt'|Hge'].
        { left; split; assumption. }
        { right; left; lia. }
      * right; right; lia.
    + subst; exists 1; lia.
    + subst; exists 1; lia.
    + exfalso; lia.
Qed.

Lemma prime_3: prime 3.
Proof.
  constructor.
  - lia.
  - intros n Hdiv.
    assert (1 < n < 3 \/ n = 1 \/ n = 3) as [H|[H|H]].
    + destruct (Z_lt_ge_dec n 3) as [Hlt|Hge].
      * destruct (Z_lt_ge_dec 1 n) as [Hlt'|Hge'].
        { left; split; assumption. }
        { right; left; lia. }
      * right; right; lia.
    + subst; exists 1; lia.
    + subst; exists 1; lia.
    + exfalso; lia.
Qed.

Lemma prime_5: prime 5.
Proof.
  constructor.
  - lia.
  - intros n Hdiv.
    assert (1 < n < 5 \/ n = 1 \/ n = 5) as [H|[H|H]].
    + destruct (Z_lt_ge_dec n 5) as [Hlt|Hge].
      * destruct (Z_lt_ge_dec 1 n) as [Hlt'|Hge'].
        { left; split; assumption. }
        { right; left; lia. }
      * right; right; lia.
    + subst; exists 1; lia.
    + subst; exists 1; lia.
    + exfalso; lia.
Qed.

Lemma prime_ge_2: forall p, prime p -> p >= 2.
Proof.
  intros p Hprime.
  destruct Hprime as [H1 H2].
  lia.
Qed.

Example test_case_5: problem_75_pre 5 -> problem_75_spec 5 false.
Proof.
  intro Hpre.
  unfold problem_75_spec.
  split.
  - intro H.
    contradict H.
    intros [p1 [p2 [p3 [Hp1 [Hp2 [Hp3 Heq]]]]]].
    assert (Hpos1: p1 >= 2) by (apply prime_ge_2; assumption).
    assert (Hpos2: p2 >= 2) by (apply prime_ge_2; assumption).
    assert (Hpos3: p3 >= 2) by (apply prime_ge_2; assumption).
    rewrite Heq in Hpre.
    nia.
  - intro H.
    reflexivity.
Qed.