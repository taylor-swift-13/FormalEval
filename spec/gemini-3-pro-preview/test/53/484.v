Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_1000001_1000001: add_spec 1000001 1000001 2000002.
Proof.
  unfold add_spec.
  reflexivity.
Qed.