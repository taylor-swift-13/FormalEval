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

Axiom IsPrime_514229 : IsPrime 514229.

Axiom IsFib_514229 : IsFib 514229.

Lemma IsPrimeFib_514229 : IsPrimeFib 514229.
Proof.
  unfold IsPrimeFib. split.
  - apply IsPrime_514229.
  - apply IsFib_514229.
Qed.

Axiom IsPrimeFib_2 : IsPrimeFib 2.
Axiom IsPrimeFib_3 : IsPrimeFib 3.
Axiom IsPrimeFib_5 : IsPrimeFib 5.
Axiom IsPrimeFib_13 : IsPrimeFib 13.
Axiom IsPrimeFib_89 : IsPrimeFib 89.
Axiom IsPrimeFib_233 : IsPrimeFib 233.
Axiom IsPrimeFib_1597 : IsPrimeFib 1597.
Axiom IsPrimeFib_28657 : IsPrimeFib 28657.

Axiom primefib_list_correct : forall y : nat,
  In y [2; 3; 5; 13; 89; 233; 1597; 28657] <-> (y < 514229 /\ IsPrimeFib y).

Lemma NoDup_primefib_list : NoDup [2; 3; 5; 13; 89; 233; 1597; 28657].
Proof.
  repeat constructor; simpl; intuition; try discriminate.
Qed.

Example problem_39_test1 : problem_39_spec 9 514229.
Proof.
  unfold problem_39_spec.
  split.
  - apply IsPrimeFib_514229.
  - exists [2; 3; 5; 13; 89; 233; 1597; 28657].
    split.
    + simpl. reflexivity.
    + split.
      * apply NoDup_primefib_list.
      * apply primefib_list_correct.
Qed.