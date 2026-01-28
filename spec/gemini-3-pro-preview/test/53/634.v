Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg9998_1000: add_spec (-9998) 1000 (-8998).
Proof.
  unfold add_spec.
  reflexivity.
Qed.