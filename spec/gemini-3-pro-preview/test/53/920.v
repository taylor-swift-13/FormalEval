Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg: add_spec (-999998) (-1000000000000000000002) (-1000000000000001000000).
Proof.
  unfold add_spec.
  reflexivity.
Qed.