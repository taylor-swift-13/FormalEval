Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg: add_spec (-1000002) (-999999) (-2000001).
Proof.
  unfold add_spec.
  reflexivity.
Qed.