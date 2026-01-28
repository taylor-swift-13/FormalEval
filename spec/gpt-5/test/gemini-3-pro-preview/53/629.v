Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_large_neg : add_spec (-98765432101234567890123456789) (-100) (-98765432101234567890123456889).
Proof.
  unfold add_spec.
  reflexivity.
Qed.