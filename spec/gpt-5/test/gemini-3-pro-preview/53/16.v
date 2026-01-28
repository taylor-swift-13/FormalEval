Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_923_369 : add_spec 923 369 1292.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.