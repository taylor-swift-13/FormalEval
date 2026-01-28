Require Import Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Psatz.
Open Scope Z_scope.

Definition problem_75_pre (a : Z) : Prop := a < 100.

Definition problem_75_spec (a : Z) (b : bool) : Prop :=
  (b = true <-> exists p1 p2 p3, prime p1 /\ prime p2 /\ prime p3 /\ a = p1 * p2 * p3).

Example test_case : problem_75_spec 22 false.
Proof.
  unfold problem_75_spec.
  split.
  - intros H. inversion H.
  - intros (p1 & p2 & p3 & Hp1 & Hp2 & Hp3 & Heq).
    apply prime_ge_2 in Hp1.
    apply prime_ge_2 in Hp2.
    apply prime_ge_2 in Hp3.
    assert (H_one_is_two : p1 = 2 \/ p2 = 2 \/ p3 = 2).
    { destruct (Z.eq_dec p1 2); [left; auto|].
      destruct (Z.eq_dec p2 2); [right; left; auto|].
      destruct (Z.eq_dec p3 2); [right; right; auto|].
      assert (p1 >= 3) by nia.
      assert (p2 >= 3) by nia.
      assert (p3 >= 3) by nia.
      nia. }
    destruct H_one_is_two as [H | [H | H]]; rewrite H in Heq.
    + assert (Heq': p2 * p3 = 11) by nia.
      assert (p2 < 4 \/ p3 < 4).
      { destruct (Z_lt_dec p2 4); [left; auto|].
        destruct (Z_lt_dec p3 4); [right; auto|].
        nia. }
      destruct H0 as [H0 | H0].
      * assert (p2 = 2 \/ p2 = 3) by nia. destruct H1; rewrite H1 in Heq'; nia.
      * assert (p3 = 2 \/ p3 = 3) by nia. destruct H1; rewrite H1 in Heq'; nia.
    + assert (Heq': p1 * p3 = 11) by nia.
      assert (p1 < 4 \/ p3 < 4).
      { destruct (Z_lt_dec p1 4); [left; auto|].
        destruct (Z_lt_dec p3 4); [right; auto|].
        nia. }
      destruct H0 as [H0 | H0].
      * assert (p1 = 2 \/ p1 = 3) by nia. destruct H1; rewrite H1 in Heq'; nia.
      * assert (p3 = 2 \/ p3 = 3) by nia. destruct H1; rewrite H1 in Heq'; nia.
    + assert (Heq': p1 * p2 = 11) by nia.
      assert (p1 < 4 \/ p2 < 4).
      { destruct (Z_lt_dec p1 4); [left; auto|].
        destruct (Z_lt_dec p2 4); [right; auto|].
        nia. }
      destruct H0 as [H0 | H0].
      * assert (p1 = 2 \/ p1 = 3) by nia. destruct H1; rewrite H1 in Heq'; nia.
      * assert (p2 = 2 \/ p2 = 3) by nia. destruct H1; rewrite H1 in Heq'; nia.
Qed.