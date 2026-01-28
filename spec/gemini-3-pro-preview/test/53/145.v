Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_3_neg251: add_spec 3 (-251) (-248).
Proof.
  unfold add_spec.
  reflexivity.
Qed.