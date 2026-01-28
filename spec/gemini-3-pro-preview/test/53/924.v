Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg2_98765432101234567890123456790: add_spec (-2) 98765432101234567890123456790 98765432101234567890123456788.
Proof.
  unfold add_spec.
  reflexivity.
Qed.