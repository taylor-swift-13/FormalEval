Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg98_big : add_spec (-98) 98765432101234567890123456790 98765432101234567890123456692.
Proof.
  unfold add_spec.
  reflexivity.
Qed.