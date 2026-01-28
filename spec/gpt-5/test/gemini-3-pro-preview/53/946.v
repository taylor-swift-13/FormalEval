Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg11_neg11 : add_spec (-11) (-11) (-22).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.