Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_66_98765432101234567890123456789: add_spec 66 98765432101234567890123456789 98765432101234567890123456855.
Proof.
  unfold add_spec.
  reflexivity.
Qed.