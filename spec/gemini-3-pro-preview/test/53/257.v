Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_1001_1002: add_spec 1001 1002 2003.
Proof.
  unfold add_spec.
  reflexivity.
Qed.