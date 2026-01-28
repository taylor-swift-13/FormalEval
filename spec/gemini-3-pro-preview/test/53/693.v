Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_4_neg: add_spec 4 (-1000000000000000000000) (-999999999999999999996).
Proof.
  unfold add_spec.
  reflexivity.
Qed.