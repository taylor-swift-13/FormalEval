Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg9998_neg9997 : add_spec (-9998) (-9997) (-19995).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.