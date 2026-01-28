Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_152_343: add_spec 152 343 495.
Proof.
  unfold add_spec.
  reflexivity.
Qed.