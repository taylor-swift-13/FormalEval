Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg1_neg101 : add_spec (-1) (-101) (-102).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.