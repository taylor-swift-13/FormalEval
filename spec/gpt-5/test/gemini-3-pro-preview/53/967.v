Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_999_neg1000000 : add_spec 999 (-1000000) (-999001).
Proof.
  unfold add_spec.
  reflexivity.
Qed.