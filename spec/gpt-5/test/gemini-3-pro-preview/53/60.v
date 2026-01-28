Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_570_503 : add_spec 570 503 1073.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.