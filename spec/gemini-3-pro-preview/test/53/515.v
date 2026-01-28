Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg999997_98765432101234567890123456785: add_spec (-999997) 98765432101234567890123456785 98765432101234567890122456788.
Proof.
  unfold add_spec.
  reflexivity.
Qed.