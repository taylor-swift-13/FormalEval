Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_860_376 : add_spec 860 376 1236.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.