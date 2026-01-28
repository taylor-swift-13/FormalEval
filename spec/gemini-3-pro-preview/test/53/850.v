Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_70_70: add_spec 70 70 140.
Proof.
  unfold add_spec.
  reflexivity.
Qed.