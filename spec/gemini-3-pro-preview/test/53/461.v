Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_1001_neg999996: add_spec 1001 (-999996) (-998995).
Proof.
  unfold add_spec.
  reflexivity.
Qed.