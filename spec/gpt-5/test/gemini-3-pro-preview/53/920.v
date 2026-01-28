Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_large_neg : add_spec (-999998) (-1000000000000000000002) (-1000000000000001000000).
Proof.
  unfold add_spec.
  reflexivity.
Qed.