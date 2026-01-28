Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_large: add_spec 999999999999999999 98765432101234567890123456789 98765432102234567890123456788.
Proof.
  unfold add_spec.
  reflexivity.
Qed.