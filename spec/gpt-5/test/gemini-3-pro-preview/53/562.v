Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg_10000_neg_9999 : add_spec (-10000) (-9999) (-19999).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.