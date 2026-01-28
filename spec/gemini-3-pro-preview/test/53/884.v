Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg_999995_neg_999995: add_spec (-999995) (-999995) (-1999990).
Proof.
  unfold add_spec.
  reflexivity.
Qed.