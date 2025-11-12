
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Numbers.PrimeNat.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition largest_prime_factor_spec (n : nat) (largest_prime : nat) : Prop :=
  n > 1 /\
  ~ Nat.Prime n /\
  Nat.Prime largest_prime /\
  n mod largest_prime = 0 /\
  (forall p, Nat.Prime p -> n mod p = 0 -> p <= largest_prime).
