Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_5_neg123456789098765432101234567890: add_spec 5 (-123456789098765432101234567890) (-123456789098765432101234567885).
Proof.
  unfold add_spec.
  reflexivity.
Qed.