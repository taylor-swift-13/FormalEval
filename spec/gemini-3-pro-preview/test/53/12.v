Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_123_102: add_spec 123 102 225.
Proof.
  unfold add_spec.
  reflexivity.
Qed.