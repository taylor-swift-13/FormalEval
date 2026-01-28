Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg_11_neg_999996 : add_spec (-11) (-999996) (-1000007).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.