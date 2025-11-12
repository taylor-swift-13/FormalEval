
Require Import ZArith.

Definition any_int_spec (x : Z) (y : Z) (z : Z) (result : bool) : Prop :=
  result = (x =? y + z || y =? x + z || z =? y + x).
