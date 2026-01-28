Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_610_541 : add_spec 610 541 1151.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.