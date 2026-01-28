Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg999996_98765432101234567890123456789: add_spec (-999996) 98765432101234567890123456789 98765432101234567890122456793.
Proof.
  unfold add_spec.
  reflexivity.
Qed.