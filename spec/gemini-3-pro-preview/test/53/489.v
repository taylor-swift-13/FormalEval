Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_1000001_large: add_spec 1000001 123456789098765432101234567893 123456789098765432101235567894.
Proof.
  unfold add_spec.
  reflexivity.
Qed.