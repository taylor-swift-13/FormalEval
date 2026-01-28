Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_157_479 : add_spec 157 479 636.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.