Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_5_neg_large : add_spec 5 (-999999999999999999998) (-999999999999999999993).
Proof.
  unfold add_spec.
  reflexivity.
Qed.