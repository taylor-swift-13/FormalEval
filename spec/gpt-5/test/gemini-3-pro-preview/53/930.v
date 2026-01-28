Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg100_neg9997 : add_spec (-100) (-9997) (-10097).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.