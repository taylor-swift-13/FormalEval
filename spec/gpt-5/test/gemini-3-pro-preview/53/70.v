Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_264_478 : add_spec 264 478 742.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.