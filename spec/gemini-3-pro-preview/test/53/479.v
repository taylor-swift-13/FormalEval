Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_999997_1001: add_spec 999997 1001 1000998.
Proof.
  unfold add_spec.
  reflexivity.
Qed.