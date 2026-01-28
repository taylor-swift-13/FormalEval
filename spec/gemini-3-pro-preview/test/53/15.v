Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_735_413: add_spec 735 413 1148.
Proof.
  unfold add_spec.
  reflexivity.
Qed.