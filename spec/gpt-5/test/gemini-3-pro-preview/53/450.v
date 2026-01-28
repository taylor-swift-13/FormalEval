Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_9998_big : add_spec 9998 123456789098765432101234567893 123456789098765432101234577891.
Proof.
  unfold add_spec.
  reflexivity.
Qed.