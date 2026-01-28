Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_9999_neg11 : add_spec 9999 (-11) 9988.
Proof.
  unfold add_spec.
  reflexivity.
Qed.