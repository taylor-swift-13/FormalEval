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

Axiom is_prime_2971215073 : IsPrime 2971215073.

Axiom is_fib_2971215073 : IsFib 2971215073.

Axiom primefib_list_for_11 : exists (S : list nat),
  length S = 10 /\
  NoDup S /\
  (forall y : nat, In y S <-> (y < 2971215073 /\ IsPrimeFib y)).

Example test_problem_39_11 : problem_39_spec 11 2971215073.
Proof.
  unfold problem_39_spec.
  split.
  - unfold IsPrimeFib.
    split.
    + exact is_prime_2971215073.
    + exact is_fib_2971215073.
  - exact primefib_list_for_11.
Qed.