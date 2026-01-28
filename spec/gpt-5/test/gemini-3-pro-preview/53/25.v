Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_623_593 : add_spec 623 593 1216.
Proof.
  unfold add_spec.
  reflexivity.
Qed.