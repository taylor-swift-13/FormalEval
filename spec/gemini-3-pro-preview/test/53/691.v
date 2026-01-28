Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg9_neg11: add_spec (-9) (-11) (-20).
Proof.
  unfold add_spec.
  reflexivity.
Qed.