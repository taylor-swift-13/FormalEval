Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_452_186 : add_spec 452 186 638.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.