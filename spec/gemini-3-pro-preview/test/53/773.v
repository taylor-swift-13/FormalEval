Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_70_neg999999: add_spec 70 (-999999) (-999929).
Proof.
  unfold add_spec.
  reflexivity.
Qed.