Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_428_315: add_spec 428 315 743.
Proof.
  unfold add_spec.
  reflexivity.
Qed.