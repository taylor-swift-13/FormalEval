Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg: add_spec (-1000001) (-1000002) (-2000003).
Proof.
  unfold add_spec.
  reflexivity.
Qed.