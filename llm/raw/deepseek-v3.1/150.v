
Require Import ZArith.
Require Import List.

Definition is_prime (a : Z) : Prop :=
  a >= 2 /\ forall x : Z, 2 <= x <= Z.sqrt a -> ~(Z.divide x a).

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).
