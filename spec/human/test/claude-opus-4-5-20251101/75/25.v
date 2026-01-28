Require Import Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.
Open Scope Z_scope.

Definition problem_75_pre (a : Z) : Prop := a < 100.

Definition problem_75_spec (a : Z) (b : bool) : Prop :=
  (b = true <-> exists p1 p2 p3, prime p1 /\ prime p2 /\ prime p3 /\ a = p1 * p2 * p3).

Lemma prime_ge_2 : forall p, prime p -> p >= 2.
Proof.
  intros p Hp.
  destruct Hp as [Hp1 Hp2].
  lia.
Qed.

Lemma product_of_three_primes_positive : forall p1 p2 p3,
  prime p1 -> prime p2 -> prime p3 -> p1 * p2 * p3 > 0.
Proof.
  intros p1 p2 p3 H1 H2 H3.
  assert (p1 >= 2) by (apply prime_ge_2; auto).
  assert (p2 >= 2) by (apply prime_ge_2; auto).
  assert (p3 >= 2) by (apply prime_ge_2; auto).
  nia.
Qed.

Lemma negative_not_product_of_three_primes :
  ~(exists p1 p2 p3, prime p1 /\ prime p2 /\ prime p3 /\ (-98) = p1 * p2 * p3).
Proof.
  intros [p1 [p2 [p3 [Hp1 [Hp2 [Hp3 Heq]]]]]].
  assert (Hpos: p1 * p2 * p3 > 0) by (apply product_of_three_primes_positive; auto).
  lia.
Qed.

Example test_problem_75 : problem_75_spec (-98) false.
Proof.
  unfold problem_75_spec.
  split.
  - intros H. discriminate H.
  - intros H. exfalso. apply negative_not_product_of_three_primes. exact H.
Qed.