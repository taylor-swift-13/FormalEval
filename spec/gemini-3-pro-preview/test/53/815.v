Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg100_9998: add_spec (-100) 9998 9898.
Proof.
  unfold add_spec.
  reflexivity.
Qed.