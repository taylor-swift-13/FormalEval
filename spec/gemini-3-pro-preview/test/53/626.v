Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_1_neg9999: add_spec 1 (-9999) (-9998).
Proof.
  unfold add_spec.
  reflexivity.
Qed.