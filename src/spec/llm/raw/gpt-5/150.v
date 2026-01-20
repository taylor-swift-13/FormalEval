Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zsqrt.

Open Scope Z_scope.

Definition is_prime (a : Z) : Prop :=
~ (a < 2 \/ exists x : Z, 2 <= x <= Z.sqrt a /\ Z.modulo a x = 0).

Definition x_or_y_spec (n x y r : Z) : Prop :=
(is_prime n /\ r = x) \/ (~ is_prime n /\ r = y).