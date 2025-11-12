
Require Import ZArith.
Open Scope Z_scope.

Definition any_int_spec (x y z : Z) (res : bool) : Prop :=
  res = ((x = y + z) \/ (y = x + z) \/ (z = x + y)).
