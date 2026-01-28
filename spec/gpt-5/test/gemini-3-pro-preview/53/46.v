Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_172_601 : add_spec 172 601 773.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.