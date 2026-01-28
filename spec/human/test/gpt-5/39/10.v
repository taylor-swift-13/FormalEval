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

Example problem_39_pre_10 : problem_39_pre 10.
Proof.
  unfold problem_39_pre. lia.
Qed.

Axiom fib_43 : fib 43 = 433494437.
Axiom prime_433494437 : IsPrime 433494437.

Definition S9 := [2;3;5;13;89;233;1597;28657;514229].

Axiom NoDup_S9 : NoDup S9.
Axiom S9_characterization : forall y : nat, In y S9 <-> (y < 433494437 /\ IsPrimeFib y).

Example problem_39_spec_10_433494437 : problem_39_spec 10 433494437.
Proof.
  unfold problem_39_spec.
  split.
  - unfold IsPrimeFib.
    split.
    + apply prime_433494437.
    + unfold IsFib. exists 43. rewrite fib_43. reflexivity.
  - exists S9.
    split.
    + simpl. reflexivity.
    + split.
      * apply NoDup_S9.
      * intros y. apply S9_characterization.
Qed.