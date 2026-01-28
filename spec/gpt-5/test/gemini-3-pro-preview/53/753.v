Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_4_neg98 : add_spec 4 (-98) (-94).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.