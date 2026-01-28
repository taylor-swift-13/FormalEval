Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg100_neg100 : add_spec (-100) (-100) (-200).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.