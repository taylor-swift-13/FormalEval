Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_10002_10003: add_spec 10002 10003 20005.
Proof.
  unfold add_spec.
  reflexivity.
Qed.