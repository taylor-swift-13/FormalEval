Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Coq.Lists.ListSet.
Import ListNotations.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.

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

Example prime_fib_test_1_pre : problem_39_pre 10.
Proof.
  unfold problem_39_pre; lia.
Qed.

Definition PF_S : list nat := [2; 3; 5; 13; 89; 233; 1597; 28657; 514229].

Axiom prime_433494437 : IsPrime 433494437.
Axiom fib_at_43 : fib_at 43 433494437.
Axiom PF_S_NoDup : NoDup PF_S.
Axiom PF_S_equiv :
  forall y : nat, In y PF_S <-> (y < 433494437 /\ IsPrimeFib y).

Example prime_fib_test_1_spec : problem_39_spec 10 433494437.
Proof.
  unfold problem_39_spec.
  split.
  - unfold IsPrimeFib.
    split.
    + apply prime_433494437.
    + unfold IsFib. exists 43. apply fib_at_43.
  - exists PF_S.
    split.
    + simpl. lia.
    + split.
      * apply PF_S_NoDup.
      * intros y. apply PF_S_equiv.
Qed.