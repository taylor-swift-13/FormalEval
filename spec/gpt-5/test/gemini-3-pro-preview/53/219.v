Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_999998_999999 : add_spec 999998 999999 1999997.
Proof.
  unfold add_spec.
  reflexivity.
Qed.