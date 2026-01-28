Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_8_neg15: add_spec 8 (-15) (-7).
Proof.
  unfold add_spec.
  reflexivity.
Qed.