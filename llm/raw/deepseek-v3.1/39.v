
Require Import ZArith.
Require Import List.
Require Import Psatz.

Fixpoint fibonacci (n : nat) : Z :=
  match n with
  | O => 0
  | S O => 1
  | S (S m as p) => fibonacci m + fibonacci p
  end.

Definition is_prime (n : Z) : Prop :=
  n > 1 /\ (forall p : Z, 1 < p < n -> ~ (p | n)).

Definition prime_fib_spec (n : nat) (result : Z) : Prop :=
  exists (fib_seq : list Z) (prime_fibs : list Z),
    fib_seq = map fibonacci (seq 0 (S (2 * n))) /\
    prime_fibs = filter (fun x => is_prime x) fib_seq /\
    nth (pred (Z.to_nat (Z.of_nat n))) prime_fibs 0 = result /\
    result <> 0.
