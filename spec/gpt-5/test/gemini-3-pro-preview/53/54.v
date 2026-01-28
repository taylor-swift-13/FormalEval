Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_152_343 : add_spec 152 343 495.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.