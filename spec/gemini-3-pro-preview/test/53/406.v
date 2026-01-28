Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_big: add_spec 98765432101234567890123456786 98765432101234567890123456786 197530864202469135780246913572.
Proof.
  unfold add_spec.
  reflexivity.
Qed.