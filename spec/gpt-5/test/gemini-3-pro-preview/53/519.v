Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg_999999_neg_1000002 : add_spec (-999999) (-1000002) (-2000001).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.