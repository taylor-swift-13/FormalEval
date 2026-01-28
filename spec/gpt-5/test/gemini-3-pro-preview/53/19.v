Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_540_790 : add_spec 540 790 1330.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.