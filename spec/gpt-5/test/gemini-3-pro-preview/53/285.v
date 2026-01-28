Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_9998_neg10000 : add_spec 9998 (-10000) (-2).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.