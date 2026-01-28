Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_large : add_spec 123456789098765432101234567892 1000000000000000000003 123456790098765432101234567895.
Proof.
  unfold add_spec.
  reflexivity.
Qed.