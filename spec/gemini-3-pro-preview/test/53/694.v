Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_9998_9999: add_spec 9998 9999 19997.
Proof.
  unfold add_spec.
  reflexivity.
Qed.