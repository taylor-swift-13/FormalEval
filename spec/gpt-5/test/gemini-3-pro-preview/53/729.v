Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg2_neg102 : add_spec (-2) (-102) (-104).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.