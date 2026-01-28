Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Coq.Lists.ListSet.
Require Import Lia.
Import ListNotations.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => match n' with
            | 0 => 1
            | S n'' => fib n' + fib n''
            end
  end.

Definition IsFib (n : nat) : Prop := exists i : nat, fib i = n.

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

Axiom IsPrimeFib_99194853094755497 : IsPrimeFib 99194853094755497.
Axiom PrimeFibListLessThan_99194853094755497 :
  exists (S : list nat),
    length S = 11 /\
    NoDup S /\
    (forall y : nat, In y S <-> (y < 99194853094755497 /\ IsPrimeFib y)).

Example problem_39_pre_12 : problem_39_pre 12.
Proof.
  unfold problem_39_pre. lia.
Qed.

Example problem_39_spec_12_99194853094755497 : problem_39_spec 12 99194853094755497.
Proof.
  unfold problem_39_spec.
  split.
  - apply IsPrimeFib_99194853094755497.
  - destruct PrimeFibListLessThan_99194853094755497 as [S [Hlen [Hndup Hmem]]].
    exists S.
    split.
    + replace (12 - 1) with 11 by lia. exact Hlen.
    + split; [exact Hndup | exact Hmem].
Qed.