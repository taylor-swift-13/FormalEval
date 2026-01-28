Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_999995_999996 : add_spec 999995 999996 1999991.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.