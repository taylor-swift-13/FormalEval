Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_418_549 : add_spec 418 549 967.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.