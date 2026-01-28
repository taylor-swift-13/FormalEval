Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg999997_neg10000: add_spec (-999997) (-10000) (-1009997).
Proof.
  unfold add_spec.
  reflexivity.
Qed.