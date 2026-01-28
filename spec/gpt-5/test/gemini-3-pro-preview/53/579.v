Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_10003_10002 : add_spec 10003 10002 20005.
Proof.
  unfold add_spec.
  reflexivity.
Qed.