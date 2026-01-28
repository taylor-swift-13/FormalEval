Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_172_601: add_spec 172 601 773.
Proof.
  unfold add_spec.
  reflexivity.
Qed.