Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg1000_8: add_spec (-1000) 8 (-992).
Proof.
  unfold add_spec.
  reflexivity.
Qed.