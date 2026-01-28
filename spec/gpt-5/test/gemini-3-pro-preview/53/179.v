Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg250_neg250 : add_spec (-250) (-250) (-500).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.