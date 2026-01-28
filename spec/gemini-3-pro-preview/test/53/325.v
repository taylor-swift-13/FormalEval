Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg_10000_neg_999998: add_spec (-10000) (-999998) (-1009998).
Proof.
  unfold add_spec.
  reflexivity.
Qed.