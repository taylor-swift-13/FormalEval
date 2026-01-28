Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_10000_neg_large: add_spec 10000 (-123456789098765432101234567890) (-123456789098765432101234557890).
Proof.
  unfold add_spec.
  reflexivity.
Qed.