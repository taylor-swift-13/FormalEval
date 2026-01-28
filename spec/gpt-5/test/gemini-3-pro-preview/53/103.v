Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_950_134 : add_spec 950 134 1084.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.