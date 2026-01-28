Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_true_7 : add_spec 1 7 8.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.