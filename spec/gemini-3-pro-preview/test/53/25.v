Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_623_593: add_spec 623 593 1216.
Proof.
  unfold add_spec.
  reflexivity.
Qed.