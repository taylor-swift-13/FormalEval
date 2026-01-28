Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg_1000000000000000000000_10002: add_spec (-1000000000000000000000) 10002 (-999999999999999989998).
Proof.
  unfold add_spec.
  reflexivity.
Qed.