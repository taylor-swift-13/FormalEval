Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_249_665 : add_spec 249 665 914.
Proof.
  unfold add_spec.
  reflexivity.
Qed.