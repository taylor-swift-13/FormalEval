Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_0_10002: add_spec 0 10002 10002.
Proof.
  unfold add_spec.
  reflexivity.
Qed.