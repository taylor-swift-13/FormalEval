Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg10_neg10 : add_spec (-10) (-10) (-20).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.