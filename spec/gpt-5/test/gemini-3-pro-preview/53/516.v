Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg_10001_neg_1000002 : add_spec (-10001) (-1000002) (-1010003).
Proof.
  unfold add_spec.
  reflexivity.
Qed.