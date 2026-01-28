Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_999998_999996 : add_spec 999998 999996 1999994.
Proof.
  unfold add_spec.
  reflexivity.
Qed.