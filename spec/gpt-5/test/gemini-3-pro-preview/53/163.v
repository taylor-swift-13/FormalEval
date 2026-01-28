Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_1_neg251 : add_spec 1 (-251) (-250).
Proof.
  unfold add_spec.
  reflexivity.
Qed.