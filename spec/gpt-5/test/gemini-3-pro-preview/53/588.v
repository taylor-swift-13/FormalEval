Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg_limits : add_spec (-2147483648) (-1) (-2147483649).
Proof.
  unfold add_spec.
  reflexivity.
Qed.