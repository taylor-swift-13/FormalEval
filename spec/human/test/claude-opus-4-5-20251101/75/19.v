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

Lemma twentysix_not_product_of_three_primes :
  ~(exists p1 p2 p3, prime p1 /\ prime p2 /\ prime p3 /\ 26 = p1 * p2 * p3).
Proof.
  intros [p1 [p2 [p3 [Hp1 [Hp2 [Hp3 Heq]]]]]].
  assert (H1: p1 >= 2) by (apply prime_ge_2; auto).
  assert (H2: p2 >= 2) by (apply prime_ge_2; auto).
  assert (H3: p3 >= 2) by (apply prime_ge_2; auto).
  assert (Hbound: p1 <= 6) by nia.
  assert (Hbound2: p2 <= 6) by nia.
  assert (Hbound3: p3 <= 6) by nia.
  assert (p1 = 2 \/ p1 = 3 \/ p1 = 4 \/ p1 = 5 \/ p1 = 6) by lia.
  assert (p2 = 2 \/ p2 = 3 \/ p2 = 4 \/ p2 = 5 \/ p2 = 6) by lia.
  assert (p3 = 2 \/ p3 = 3 \/ p3 = 4 \/ p3 = 5 \/ p3 = 6) by lia.
  destruct H as [Hp1_2 | [Hp1_3 | [Hp1_4 | [Hp1_5 | Hp1_6]]]];
  destruct H0 as [Hp2_2 | [Hp2_3 | [Hp2_4 | [Hp2_5 | Hp2_6]]]];
  destruct H4 as [Hp3_2 | [Hp3_3 | [Hp3_4 | [Hp3_5 | Hp3_6]]]];
  subst; try lia;
  try (destruct Hp1 as [Hp1a Hp1b]; specialize (Hp1b 2); assert (2 | 4) by (exists 2; lia); specialize (Hp1b H); lia);
  try (destruct Hp1 as [Hp1a Hp1b]; specialize (Hp1b 2); assert (2 | 6) by (exists 3; lia); specialize (Hp1b H); lia);
  try (destruct Hp2 as [Hp2a Hp2b]; specialize (Hp2b 2); assert (2 | 4) by (exists 2; lia); specialize (Hp2b H); lia);
  try (destruct Hp2 as [Hp2a Hp2b]; specialize (Hp2b 2); assert (2 | 6) by (exists 3; lia); specialize (Hp2b H); lia);
  try (destruct Hp3 as [Hp3a Hp3b]; specialize (Hp3b 2); assert (2 | 4) by (exists 2; lia); specialize (Hp3b H); lia);
  try (destruct Hp3 as [Hp3a Hp3b]; specialize (Hp3b 2); assert (2 | 6) by (exists 3; lia); specialize (Hp3b H); lia).
Qed.

Example test_problem_75 : problem_75_spec 26 false.
Proof.
  unfold problem_75_spec.
  split.
  - intros H. discriminate H.
  - intros H. exfalso. apply twentysix_not_product_of_three_primes. exact H.
Qed.