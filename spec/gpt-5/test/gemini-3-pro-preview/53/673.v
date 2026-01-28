Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg8_neg9999 : add_spec (-8) (-9999) (-10007).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.