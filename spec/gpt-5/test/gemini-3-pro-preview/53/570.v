Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_large_neg : add_spec (-999999999999999999998) (-999999999999999999997) (-1999999999999999999995).
Proof.
  unfold add_spec.
  reflexivity.
Qed.