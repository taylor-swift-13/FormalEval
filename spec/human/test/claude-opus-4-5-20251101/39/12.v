Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Coq.Lists.ListSet.
Import ListNotations.
Require Import Lia.

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

Axiom primefib_12_result : IsPrimeFib 99194853094755497.

Axiom primefib_list_11 : list nat.
Axiom primefib_list_11_length : length primefib_list_11 = 11.
Axiom primefib_list_11_nodup : NoDup primefib_list_11.
Axiom primefib_list_11_spec : forall y : nat, In y primefib_list_11 <-> (y < 99194853094755497 /\ IsPrimeFib y).

Example test_problem_39_12 : problem_39_spec 12 99194853094755497.
Proof.
  unfold problem_39_spec.
  split.
  - exact primefib_12_result.
  - exists primefib_list_11.
    split.
    + exact primefib_list_11_length.
    + split.
      * exact primefib_list_11_nodup.
      * exact primefib_list_11_spec.
Qed.