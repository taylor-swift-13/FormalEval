Require Import Coq.Arith.Arith.

Definition divides (d n : int) : Prop :=
  exists k : int, n = d * k.

Definition is_prime (p : int) : Prop :=
  2 <= p /\ forall d : int, divides d p -> d = 1 \/ d = p.

Definition largest_prime_factor_spec (n : int) (p : int) : Prop :=
  n > 1 /\ ~ is_prime n ->
  is_prime p /\ divides p n /\
  forall q : int, is_prime q /\ divides q n -> q <= p.