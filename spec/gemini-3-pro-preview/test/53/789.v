Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_10000_999999999999999999: add_spec 10000 999999999999999999 1000000000000009999.
Proof.
  unfold add_spec.
  reflexivity.
Qed.