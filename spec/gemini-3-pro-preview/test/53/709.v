Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg101_neg9: add_spec (-101) (-9) (-110).
Proof.
  unfold add_spec.
  reflexivity.
Qed.