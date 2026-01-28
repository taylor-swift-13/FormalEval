Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_1001_999998: add_spec 1001 999998 1000999.
Proof.
  unfold add_spec.
  reflexivity.
Qed.