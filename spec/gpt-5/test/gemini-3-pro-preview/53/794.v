Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_66_66 : add_spec 66 66 132.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.