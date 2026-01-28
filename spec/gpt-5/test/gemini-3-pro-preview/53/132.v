Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg1000_10 : add_spec (-1000) 10 (-990).
Proof.
  unfold add_spec.
  reflexivity.
Qed.