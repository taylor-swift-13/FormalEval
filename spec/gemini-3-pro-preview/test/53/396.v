Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_999999999999999999997_0: add_spec 999999999999999999997 0 999999999999999999997.
Proof.
  unfold add_spec.
  reflexivity.
Qed.