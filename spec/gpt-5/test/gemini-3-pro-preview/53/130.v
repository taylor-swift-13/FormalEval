Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg6_neg8 : add_spec (-6) (-8) (-14).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.