Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_9999_9999 : add_spec 9999 9999 19998.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.