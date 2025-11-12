
Require Import ZArith.
Require Import List.
Require Import Bool.

Definition largest_prime_factor_spec (n : Z) (result : Z) : Prop :=
  n > 1 /\
  (exists i : Z, 1 < i < n /\ (forall j : Z, 1 < j < i -> ~ (n mod j = 0))) /\
  result > 1 /\
  (n mod result = 0) /\
  (forall p : Z, result < p < n -> ~ ((n mod p = 0) /\ (forall d : Z, 1 < d < p -> ~ (p mod d = 0)))).
