Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_946_559 : add_spec 946 559 1505.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.