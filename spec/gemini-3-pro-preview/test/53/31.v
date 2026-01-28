Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_157_479: add_spec 157 479 636.
Proof.
  unfold add_spec.
  reflexivity.
Qed.