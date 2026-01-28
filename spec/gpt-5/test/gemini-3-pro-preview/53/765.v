Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_1_neg999999 : add_spec 1 (-999999) (-999998).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.