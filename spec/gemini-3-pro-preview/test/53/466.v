Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_98765432101234567890123456791_4: add_spec 98765432101234567890123456791 4 98765432101234567890123456795.
Proof.
  unfold add_spec.
  reflexivity.
Qed.