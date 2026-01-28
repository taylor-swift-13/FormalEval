Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_0_9998 : add_spec 0 9998 9998.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.