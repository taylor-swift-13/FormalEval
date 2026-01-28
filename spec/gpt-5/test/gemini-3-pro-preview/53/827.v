Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg8_neg999998 : add_spec (-8) (-999998) (-1000006).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.