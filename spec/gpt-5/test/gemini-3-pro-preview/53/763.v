Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg10_big : add_spec (-10) 98765432101234567890123456791 98765432101234567890123456781.
Proof.
  unfold add_spec.
  reflexivity.
Qed.