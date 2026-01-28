Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg999997_9999 : add_spec (-999997) 9999 (-989998).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.