Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_5_neg100: add_spec 5 (-100) (-95).
Proof.
  unfold add_spec.
  reflexivity.
Qed.