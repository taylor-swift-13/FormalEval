Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg999998_999999999999999999999: add_spec (-999998) 999999999999999999999 999999999999999000001.
Proof.
  unfold add_spec.
  reflexivity.
Qed.