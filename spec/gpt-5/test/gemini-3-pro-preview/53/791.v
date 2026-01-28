Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg : add_spec (-101) (-999999999999999999999) (-1000000000000000000100).
Proof.
  unfold add_spec.
  reflexivity.
Qed.