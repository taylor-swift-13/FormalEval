Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg15_neg15: add_spec (-15) (-15) (-30).
Proof.
  unfold add_spec.
  reflexivity.
Qed.