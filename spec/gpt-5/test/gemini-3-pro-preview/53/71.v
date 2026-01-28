Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_57_615 : add_spec 57 615 672.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.