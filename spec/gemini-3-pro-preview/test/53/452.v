Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_9999_98765432101234567890123456787: add_spec 9999 98765432101234567890123456787 98765432101234567890123466786.
Proof.
  unfold add_spec.
  reflexivity.
Qed.