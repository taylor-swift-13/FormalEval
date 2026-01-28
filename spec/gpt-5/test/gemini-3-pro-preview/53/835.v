Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg9997_neg9998 : add_spec (-9997) (-9998) (-19995).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.