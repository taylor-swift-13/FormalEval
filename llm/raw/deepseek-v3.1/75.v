
Require Import ZArith.
Require Import List.
Require Import Bool.

Definition is_prime (n : Z) : Prop :=
  n > 1 /\ forall k, 1 < k < n -> ~ (k | n).

Definition is_multiply_prime_spec (a : Z) : Prop :=
  exists p q r : Z, is_prime p /\ is_prime q /\ is_prime r /\ a = p * q * r.
