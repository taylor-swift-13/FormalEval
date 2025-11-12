Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Prime.
Require Import Coq.Bool.Bool.

Definition is_multiply_prime_spec (a : nat) (b : bool) : Prop :=
  (a <= 1 -> b = false) /\
  (1 < a -> (b = true <-> exists p q r, prime p /\ prime q /\ prime r /\ a = p * q * r)).