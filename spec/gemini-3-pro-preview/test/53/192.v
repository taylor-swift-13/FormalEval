Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_9_neg13: add_spec 9 (-13) (-4).
Proof.
  unfold add_spec.
  reflexivity.
Qed.