Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_999998_999997 : add_spec 999998 999997 1999995.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.