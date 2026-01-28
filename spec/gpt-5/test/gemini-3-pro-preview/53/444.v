Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_case_2 : add_spec (-123456789098765432101234567891) 98765432101234567890123456790 (-24691356997530864211111111101).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.