Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg_999997_neg_999996: add_spec (-999997) (-999996) (-1999993).
Proof.
  unfold add_spec.
  reflexivity.
Qed.