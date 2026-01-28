Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg999998_neg9: add_spec (-999998) (-9) (-1000007).
Proof.
  unfold add_spec.
  reflexivity.
Qed.