Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg8_big : add_spec (-8) 1000000000000000000000 999999999999999999992.
Proof.
  unfold add_spec.
  reflexivity.
Qed.