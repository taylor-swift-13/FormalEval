Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_large: add_spec 123456789098765432101234567889 98765432101234567890123456789 222222221199999999991358024678.
Proof.
  unfold add_spec.
  reflexivity.
Qed.