Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg1000000_neg101 : add_spec (-1000000) (-101) (-1000101).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.