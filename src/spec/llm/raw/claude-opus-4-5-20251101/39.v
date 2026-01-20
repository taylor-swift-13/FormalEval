
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n > 1 /\ forall d : Z, 1 < d < n -> Z.rem n d <> 0.

Fixpoint fib (n : nat) : Z :=
  match n with
  | O => 0
  | S O => 1
  | S (S m as p) => fib p + fib m
  end.

Definition is_fibonacci (n : Z) : Prop :=
  exists k : nat, fib k = n.

Definition is_prime_fib (n : Z) : Prop :=
  is_fibonacci n /\ is_prime n.

Fixpoint nth_prime_fib_aux (count : nat) (idx : nat) : Z :=
  match count with
  | O => 0
  | S c => 
    let f := fib idx in
    if (f >? 1) then
      match count with
      | S O => f
      | _ => nth_prime_fib_aux c (S idx)
      end
    else
      nth_prime_fib_aux count (S idx)
  end.

Definition prime_fib_spec (n : nat) (result : Z) : Prop :=
  n > 0 /\
  is_prime_fib result /\
  exists prime_fibs : list Z,
    (forall z, In z prime_fibs -> is_prime_fib z) /\
    length prime_fibs = n /\
    (forall i j, (i < j)%nat -> (j < n)%nat -> 
      nth i prime_fibs 0 < nth j prime_fibs 0) /\
    nth (n - 1) prime_fibs 0 = result /\
    (forall z, is_prime_fib z -> z < result -> In z prime_fibs).
