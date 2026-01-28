Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_287_494: add_spec 287 494 781.
Proof.
  unfold add_spec.
  reflexivity.
Qed.