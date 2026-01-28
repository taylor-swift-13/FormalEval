Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_183_272 : add_spec 183 272 455.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.