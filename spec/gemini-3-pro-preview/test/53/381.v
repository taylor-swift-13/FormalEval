Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_large: add_spec 10002 98765432101234567890123456787 98765432101234567890123466789.
Proof.
  unfold add_spec.
  reflexivity.
Qed.