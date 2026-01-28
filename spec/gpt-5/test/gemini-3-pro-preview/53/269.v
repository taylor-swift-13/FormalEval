Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_large : add_spec 98765432101234567890123456787%Z (-123456789098765432101234567890%Z) (-24691356997530864211111111103%Z).
Proof.
  unfold add_spec.
  reflexivity.
Qed.