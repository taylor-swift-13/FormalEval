Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_570_503: add_spec 570 503 1073.
Proof.
  unfold add_spec.
  reflexivity.
Qed.