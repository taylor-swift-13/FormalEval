Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_3_4 : add_spec 3 4 7.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.