Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg999997_neg8: add_spec (-999997) (-8) (-1000005).
Proof.
  unfold add_spec.
  reflexivity.
Qed.