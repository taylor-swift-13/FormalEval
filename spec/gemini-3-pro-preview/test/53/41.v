Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_610_541: add_spec 610 541 1151.
Proof.
  unfold add_spec.
  reflexivity.
Qed.