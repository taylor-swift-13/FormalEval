Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_345_523 : add_spec 345 523 868.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.