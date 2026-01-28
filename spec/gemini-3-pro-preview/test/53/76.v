Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_314_7: add_spec 314 7 321.
Proof.
  unfold add_spec.
  reflexivity.
Qed.