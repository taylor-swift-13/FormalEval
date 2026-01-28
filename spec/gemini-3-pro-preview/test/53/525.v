Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_large: add_spec (-123456789098765432101234567890) 98765432101234567890123456785 (-24691356997530864211111111105).
Proof.
  unfold add_spec.
  reflexivity.
Qed.