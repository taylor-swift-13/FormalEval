Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg_1000000_large: add_spec (-1000000) 123456789098765432101234567890 123456789098765432101233567890.
Proof.
  unfold add_spec.
  reflexivity.
Qed.