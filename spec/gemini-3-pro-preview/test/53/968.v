Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_999999_neg: add_spec 999999 (-999999999999999999998) (-999999999999998999999).
Proof.
  unfold add_spec.
  reflexivity.
Qed.