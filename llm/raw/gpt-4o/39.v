
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Definition is_prime (n : Z) : Prop :=
  n > 1 /\
  forall d : Z, 1 < d < n -> n mod d <> 0.

Fixpoint fib (n : nat) : Z :=
  match n with
  | 0 => 0
  | 1 => 1
  | S n' => fib n' + fib (n' - 1)
  end.

Definition is_fib (x : Z) : Prop :=
  exists n : nat, fib n = x.

Definition prime_fib_spec (n : nat) (result : Z) : Prop :=
  is_prime result /\
  is_fib result /\
  (forall k : nat, k < n -> exists x : Z, is_prime x /\ is_fib x /\ x < result).
