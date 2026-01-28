Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_7_neg999997: add_spec 7 (-999997) (-999990).
Proof.
  unfold add_spec.
  reflexivity.
Qed.