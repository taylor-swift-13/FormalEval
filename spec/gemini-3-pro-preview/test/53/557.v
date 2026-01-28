Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg1000000_big: add_spec (-1000000) 98765432101234567890123456789 98765432101234567890122456789.
Proof.
  unfold add_spec.
  reflexivity.
Qed.