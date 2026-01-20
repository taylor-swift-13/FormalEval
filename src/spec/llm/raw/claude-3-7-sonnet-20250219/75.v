
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.

Definition is_prime (n : Z) : Prop :=
  2 <= n /\ forall d : Z, 2 <= d < n -> n mod d <> 0.

Definition is_multiply_prime_spec (a : Z) (res : bool) : Prop :=
  a < 100 /\
  (res = true <-> 
    exists p1 p2 p3 : Z,
      is_prime p1 /\ is_prime p2 /\ is_prime p3 /\
      a = p1 * p2 * p3).
