
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S m => match m with
           | 0 => 1
           | S k => fib m + fib k
           end
  end.

Definition is_fib (x : nat) : Prop :=
  exists n, fib n = x.

Definition is_prime_fib (x : nat) : Prop :=
  is_fib x /\ Prime x.

Inductive nth_prime_fib : nat -> nat -> Prop :=
| nth_first : forall p,
    is_prime_fib p ->
    (forall q, q < p -> ~ is_prime_fib q) ->
    nth_prime_fib 1 p
| nth_next : forall n prev curr,
    nth_prime_fib n prev ->
    is_prime_fib curr ->
    prev < curr ->
    (forall q, prev < q /\ q < curr -> ~ is_prime_fib q) ->
    nth_prime_fib (S n) curr.

Definition prime_fib_spec (n : nat) (result : nat) : Prop :=
  nth_prime_fib n result.
