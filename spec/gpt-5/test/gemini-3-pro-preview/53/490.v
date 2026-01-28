Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_1002_neg9999 : add_spec 1002 (-9999) (-8997).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.