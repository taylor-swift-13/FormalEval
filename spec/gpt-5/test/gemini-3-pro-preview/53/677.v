Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_5_neg100 : add_spec 5 (-100) (-95).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.