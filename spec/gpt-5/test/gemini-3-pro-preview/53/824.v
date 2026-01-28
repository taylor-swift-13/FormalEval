Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_9998_999999999999999999998 : add_spec 9998 999999999999999999998 1000000000000000009996.
Proof.
  unfold add_spec.
  reflexivity.
Qed.