Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg10_1 : add_spec (-10) 1 (-9).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.