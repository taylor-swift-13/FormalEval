Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_1002_1002: add_spec 1002 1002 2004.
Proof.
  unfold add_spec.
  reflexivity.
Qed.