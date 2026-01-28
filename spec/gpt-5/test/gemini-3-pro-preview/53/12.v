Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_123_102 : add_spec 123 102 225.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.