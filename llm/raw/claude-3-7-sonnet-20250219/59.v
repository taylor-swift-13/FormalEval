
Require Import Coq.Arith.Arith.
Require Import Coq.Numbers.Primes.Prime.

Definition largest_prime_factor_spec (n : nat) (p : nat) : Prop :=
  n > 1 /\
  prime p /\
  p < n /\
  Nat.divide p n /\
  (forall q : nat, prime q -> Nat.divide q n -> q <= p).
