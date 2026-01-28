Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_91_789 : add_spec 91 789 880.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.