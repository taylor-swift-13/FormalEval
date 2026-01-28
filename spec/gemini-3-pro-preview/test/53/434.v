Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_123456789098765432101234567890_1000000: add_spec 123456789098765432101234567890 1000000 123456789098765432101235567890.
Proof.
  unfold add_spec.
  reflexivity.
Qed.