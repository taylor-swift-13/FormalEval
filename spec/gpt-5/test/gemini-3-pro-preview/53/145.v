Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_3_neg251 : add_spec 3 (-251) (-248).
Proof.
  unfold add_spec.
  reflexivity.
Qed.