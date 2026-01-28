Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg999996_neg999996 : add_spec (-999996) (-999996) (-1999992).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.