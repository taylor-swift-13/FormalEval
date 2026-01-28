Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_large : add_spec 98765432101234567890123456790 (-10000) 98765432101234567890123446790.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.