Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg_1000001_neg_999998: add_spec (-1000001) (-999998) (-1999999).
Proof.
  unfold add_spec.
  reflexivity.
Qed.