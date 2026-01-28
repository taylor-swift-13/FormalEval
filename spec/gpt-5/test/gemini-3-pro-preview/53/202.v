Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg13_neg15 : add_spec (-13) (-15) (-28).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.