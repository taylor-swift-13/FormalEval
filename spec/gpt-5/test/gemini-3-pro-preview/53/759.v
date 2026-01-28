Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_71_71 : add_spec 71 71 142.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.