Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg1000000_neg1000001 : add_spec (-1000000) (-1000001) (-2000001).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.