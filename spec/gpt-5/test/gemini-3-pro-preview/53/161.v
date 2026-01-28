Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg16_neg16 : add_spec (-16) (-16) (-32).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.