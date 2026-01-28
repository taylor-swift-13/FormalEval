Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg100_96: add_spec (-100) 96 (-4).
Proof.
  unfold add_spec.
  reflexivity.
Qed.