Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_270_420 : add_spec 270 420 690.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.