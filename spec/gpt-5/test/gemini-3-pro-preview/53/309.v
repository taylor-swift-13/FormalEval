Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg_999998_neg_98 : add_spec (-999998) (-98) (-1000096).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.