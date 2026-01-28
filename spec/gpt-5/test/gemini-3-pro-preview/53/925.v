Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg12_neg12 : add_spec (-12) (-12) (-24).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.