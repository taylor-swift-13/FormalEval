Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_923_369: add_spec 923 369 1292.
Proof.
  unfold add_spec.
  reflexivity.
Qed.