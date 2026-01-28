Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg_999997_neg_10000 : add_spec (-999997) (-10000) (-1009997).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.