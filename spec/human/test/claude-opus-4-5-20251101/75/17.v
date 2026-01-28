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

Lemma twenty_two_not_product_of_three_primes :
  ~(exists p1 p2 p3, prime p1 /\ prime p2 /\ prime p3 /\ 22 = p1 * p2 * p3).
Proof.
  intros [p1 [p2 [p3 [Hp1 [Hp2 [Hp3 Heq]]]]]].
  assert (H1: p1 >= 2) by (apply prime_ge_2; auto).
  assert (H2: p2 >= 2) by (apply prime_ge_2; auto).
  assert (H3: p3 >= 2) by (apply prime_ge_2; auto).
  assert (Hle: p1 * p2 * p3 <= 22) by lia.
  assert (Hp1_le: p1 <= 5) by nia.
  assert (Hp2_le: p2 <= 5) by nia.
  assert (Hp3_le: p3 <= 5) by nia.
  assert (p1 = 2 \/ p1 = 3 \/ p1 = 5) as Hp1_cases.
  { destruct Hp1 as [Hp1a Hp1b].
    assert (p1 <> 4).
    { intro. subst. specialize (Hp1b 2). assert (2 < 4) by lia.
      assert (Z.divide 2 4) by (exists 2; lia). apply Hp1b in H0; lia. }
    lia. }
  assert (p2 = 2 \/ p2 = 3 \/ p2 = 5) as Hp2_cases.
  { destruct Hp2 as [Hp2a Hp2b].
    assert (p2 <> 4).
    { intro. subst. specialize (Hp2b 2). assert (2 < 4) by lia.
      assert (Z.divide 2 4) by (exists 2; lia). apply Hp2b in H0; lia. }
    lia. }
  assert (p3 = 2 \/ p3 = 3 \/ p3 = 5) as Hp3_cases.
  { destruct Hp3 as [Hp3a Hp3b].
    assert (p3 <> 4).
    { intro. subst. specialize (Hp3b 2). assert (2 < 4) by lia.
      assert (Z.divide 2 4) by (exists 2; lia). apply Hp3b in H0; lia. }
    lia. }
  destruct Hp1_cases as [Hp1_eq | [Hp1_eq | Hp1_eq]];
  destruct Hp2_cases as [Hp2_eq | [Hp2_eq | Hp2_eq]];
  destruct Hp3_cases as [Hp3_eq | [Hp3_eq | Hp3_eq]];
  subst; lia.
Qed.

Example test_problem_75 : problem_75_spec 22 false.
Proof.
  unfold problem_75_spec.
  split.
  - intros H. discriminate H.
  - intros H. exfalso. apply twenty_two_not_product_of_three_primes. exact H.
Qed.