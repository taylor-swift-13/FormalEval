Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_342_129 : add_spec 342 129 471.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.