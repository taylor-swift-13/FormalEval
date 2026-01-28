Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_3_3 : add_spec 3 3 6.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.