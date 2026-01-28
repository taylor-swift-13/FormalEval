Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_999997_1000000000000000000001: add_spec 999997 1000000000000000000001 1000000000000000999998.
Proof.
  unfold add_spec.
  reflexivity.
Qed.