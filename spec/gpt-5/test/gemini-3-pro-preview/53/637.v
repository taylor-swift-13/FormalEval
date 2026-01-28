Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg9_neg9 : add_spec (-9) (-9) (-18).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.