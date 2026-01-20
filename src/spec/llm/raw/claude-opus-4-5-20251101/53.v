
Require Import ZArith.

Definition add_spec (x : Z) (y : Z) (result : Z) : Prop :=
  result = x + y.
