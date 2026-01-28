Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_314_7 : add_spec 314 7 321.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.