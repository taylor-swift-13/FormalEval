Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg_large : add_spec (-1000000000000000000002) (-1000000000000000000002) (-2000000000000000000004).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.