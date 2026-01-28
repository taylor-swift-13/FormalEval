Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg9999_big : add_spec (-9999) 1000000000000000000000 999999999999999990001.
Proof.
  unfold add_spec.
  reflexivity.
Qed.