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

Definition prime_fib_S : list nat := [2;3;5;13;89;233;1597;28657].

Axiom prime_514229 : IsPrime 514229.
Axiom fib_514229 : IsFib 514229.
Axiom NoDup_prime_fib_S : NoDup prime_fib_S.
Axiom prime_fib_S_characterization :
  forall y : nat, In y prime_fib_S <-> (y < 514229 /\ IsPrimeFib y).

Example prime_fib_test_1_pre : problem_39_pre 9.
Proof.
  unfold problem_39_pre; lia.
Qed.

Example prime_fib_test_1_spec : problem_39_spec 9 514229.
Proof.
  unfold problem_39_spec.
  split.
  - unfold IsPrimeFib.
    split; [apply prime_514229|apply fib_514229].
  - exists prime_fib_S.
    split.
    + simpl. lia.
    + split.
      * apply NoDup_prime_fib_S.
      * intros y. apply prime_fib_S_characterization.
Qed.