Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_9998_neg100: add_spec 9998 (-100) 9898.
Proof.
  unfold add_spec.
  reflexivity.
Qed.