Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Coq.Lists.ListSet.
Require Import Lia.
Import ListNotations.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Inductive fib_at : nat -> nat -> Prop :=
| fib_at_0 : fib_at 0 0
| fib_at_1 : fib_at 1 1
| fib_at_S : forall i a b,
    fib_at i a ->
    fib_at (S i) b ->
    fib_at (S (S i)) (a + b).

Definition IsFib (n : nat) : Prop := exists i : nat, fib_at i n.

Definition IsPrimeFib (n : nat) : Prop :=
  IsPrime n /\ IsFib n.

Definition problem_39_pre (n : nat) : Prop := (n >= 1)%nat.

Definition problem_39_spec (n r : nat) : Prop :=
  IsPrimeFib r /\
  (exists (S : list nat),
    length S = n - 1 /\
    NoDup S /\
    (forall y : nat, In y S <-> (y < r /\ IsPrimeFib y))
  ).

(* Helper lemma: 2 is prime *)
Lemma IsPrime_2 : IsPrime 2.
Proof.
  unfold IsPrime. split.
  - lia.
  - intros d Hmod.
    destruct d as [|[|[|d']]].
    + (* d = 0 *) simpl in Hmod. discriminate.
    + (* d = 1 *) left. reflexivity.
    + (* d = 2 *) right. reflexivity.
    + (* d >= 3 *)
      exfalso.
      assert (H: S (S (S d')) > 2) by lia.
      assert (H2: 2 mod S (S (S d')) = 2).
      { apply Nat.mod_small. lia. }
      rewrite H2 in Hmod. discriminate.
Qed.

(* Helper lemma: fib(3) = 2 *)
Lemma fib_at_3_2 : fib_at 3 2.
Proof.
  assert (H1: fib_at 2 1).
  { replace 1 with (0 + 1) by lia.
    apply fib_at_S.
    - apply fib_at_0.
    - apply fib_at_1. }
  replace 2 with (1 + 1) by lia.
  apply fib_at_S.
  - apply fib_at_1.
  - exact H1.
Qed.

(* Helper lemma: 2 is a Fibonacci number *)
Lemma IsFib_2 : IsFib 2.
Proof.
  unfold IsFib. exists 3. apply fib_at_3_2.
Qed.

(* Helper lemma: 2 is a prime Fibonacci number *)
Lemma IsPrimeFib_2 : IsPrimeFib 2.
Proof.
  unfold IsPrimeFib. split.
  - apply IsPrime_2.
  - apply IsFib_2.
Qed.

(* There are no prime fibonacci numbers less than 2 *)
Lemma no_primefib_below_2 : forall y, y < 2 -> ~ IsPrimeFib y.
Proof.
  intros y Hy [Hprime _].
  unfold IsPrime in Hprime.
  destruct Hprime as [Hgt1 _].
  lia.
Qed.

Example problem_39_test1 : problem_39_spec 1 2.
Proof.
  unfold problem_39_spec.
  split.
  - apply IsPrimeFib_2.
  - exists [].
    split.
    + simpl. reflexivity.
    + split.
      * constructor.
      * intros y. split.
        -- intros Hin. inversion Hin.
        -- intros [Hlt HprimeFib].
           exfalso.
           apply (no_primefib_below_2 y Hlt HprimeFib).
Qed.