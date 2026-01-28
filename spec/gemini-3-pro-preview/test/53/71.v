Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_57_615: add_spec 57 615 672.
Proof.
  unfold add_spec.
  reflexivity.
Qed.