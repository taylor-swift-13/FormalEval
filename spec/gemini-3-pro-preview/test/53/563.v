Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_7_neg999999999999999999997: add_spec 7 (-999999999999999999997) (-999999999999999999990).
Proof.
  unfold add_spec.
  reflexivity.
Qed.