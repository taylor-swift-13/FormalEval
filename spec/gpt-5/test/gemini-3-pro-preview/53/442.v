Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_999999999999999999998_999999999999999999998 : add_spec 999999999999999999998 999999999999999999998 1999999999999999999996.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.