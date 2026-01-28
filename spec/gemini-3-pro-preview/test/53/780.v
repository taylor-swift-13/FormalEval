Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg_9997_neg_1000000: add_spec (-9997) (-1000000) (-1009997).
Proof.
  unfold add_spec.
  reflexivity.
Qed.