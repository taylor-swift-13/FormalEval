Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_418_549: add_spec 418 549 967.
Proof.
  unfold add_spec.
  reflexivity.
Qed.