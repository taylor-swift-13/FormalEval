Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg11_neg10 : add_spec (-11) (-10) (-21).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.