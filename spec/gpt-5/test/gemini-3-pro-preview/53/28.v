Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_333_987 : add_spec 333 987 1320.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.