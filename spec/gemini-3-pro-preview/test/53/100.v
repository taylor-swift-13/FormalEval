Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_345_405: add_spec 345 405 750.
Proof.
  unfold add_spec.
  reflexivity.
Qed.