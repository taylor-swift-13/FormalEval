Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_9997_9997 : add_spec 9997 9997 19994.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.