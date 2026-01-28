Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg15_neg15 : add_spec (-15) (-15) (-30).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.