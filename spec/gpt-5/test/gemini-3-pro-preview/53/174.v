Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_8_neg998 : add_spec 8 (-998) (-990).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.