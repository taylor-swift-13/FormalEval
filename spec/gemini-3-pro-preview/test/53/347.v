Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg999998_9999: add_spec (-999998) 9999 (-989999).
Proof.
  unfold add_spec.
  reflexivity.
Qed.