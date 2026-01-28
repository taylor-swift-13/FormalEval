Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_large: add_spec 999999999999999999998 98765432101234567890123456789 98765433101234567890123456787.
Proof.
  unfold add_spec.
  reflexivity.
Qed.