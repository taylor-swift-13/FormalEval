Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_1_neg1 : add_spec 1 (-1) 0.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.