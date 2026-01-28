Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_9997_neg999999: add_spec 9997 (-999999) (-990002).
Proof.
  unfold add_spec.
  reflexivity.
Qed.