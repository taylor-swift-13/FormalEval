Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_569_756: add_spec 569 756 1325.
Proof.
  unfold add_spec.
  reflexivity.
Qed.