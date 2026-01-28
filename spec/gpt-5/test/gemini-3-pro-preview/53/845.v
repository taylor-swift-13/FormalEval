Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg8_neg3 : add_spec (-8) (-3) (-11).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.