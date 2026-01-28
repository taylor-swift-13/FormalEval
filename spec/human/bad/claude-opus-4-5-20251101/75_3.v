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

Lemma prime_2 : prime 2.
Proof.
  apply prime_intro.
  - lia.
  - intros n Hn.
    assert (n = 1 \/ n = 2) as [H | H] by lia; subst.
    + left. reflexivity.
    + right. reflexivity.
Qed.

Example test_problem_75 : problem_75_spec 8 true.
Proof.
  unfold problem_75_spec.
  split.
  - intros _.
    exists 2, 2, 2.
    repeat split; try apply prime_2.
    reflexivity.
  - intros _. reflexivity.
Qed.