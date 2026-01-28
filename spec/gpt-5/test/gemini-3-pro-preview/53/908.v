Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg100_96 : add_spec (-100) 96 (-4).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.