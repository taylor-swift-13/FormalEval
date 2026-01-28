Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg7_neg7 : add_spec (-7) (-7) (-14).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.