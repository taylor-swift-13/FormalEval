Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_100_neg999999: add_spec 100 (-999999) (-999899).
Proof.
  unfold add_spec.
  reflexivity.
Qed.