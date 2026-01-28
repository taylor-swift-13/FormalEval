Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg_1000000000000000000000_neg_9: add_spec (-1000000000000000000000) (-9) (-1000000000000000000009).
Proof.
  unfold add_spec.
  reflexivity.
Qed.