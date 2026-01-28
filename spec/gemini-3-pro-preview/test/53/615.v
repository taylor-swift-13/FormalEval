Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg_large: add_spec (-1000000000000000000000%Z) 98765432101234567890123456790%Z 98765431101234567890123456790%Z.
Proof.
  unfold add_spec.
  reflexivity.
Qed.