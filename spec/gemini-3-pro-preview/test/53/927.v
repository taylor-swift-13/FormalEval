Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg100_neg9999: add_spec (-100) (-9999) (-10099).
Proof.
  unfold add_spec.
  reflexivity.
Qed.