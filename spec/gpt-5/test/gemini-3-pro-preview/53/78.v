Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_25_435 : add_spec 25 435 460.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.