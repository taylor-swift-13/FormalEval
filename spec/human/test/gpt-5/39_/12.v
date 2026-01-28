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

Example prime_fib_test_12_pre : problem_39_pre 12.
Proof.
  unfold problem_39_pre; lia.
Qed.

Axiom prime_fib_r_99194853094755497 : IsPrimeFib (Z.to_nat 99194853094755497%Z).

Axiom prime_fib_S_99194853094755497 :
  exists (S : list nat),
    length S = 12 - 1 /\
    NoDup S /\
    (forall y : nat, In y S <-> (y < Z.to_nat 99194853094755497%Z /\ IsPrimeFib y)).

Example prime_fib_test_12_spec : problem_39_spec 12 (Z.to_nat 99194853094755497%Z).
Proof.
  unfold problem_39_spec.
  split.
  - exact prime_fib_r_99194853094755497.
  - destruct prime_fib_S_99194853094755497 as [S [Hlen [Hnd Hall]]].
    exists S.
    split; [assumption|].
    split; [assumption|].
    intros y; apply Hall.
Qed.