Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_473_244 : add_spec 473 244 717.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.