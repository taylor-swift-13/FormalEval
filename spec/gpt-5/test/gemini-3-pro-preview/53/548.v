Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_123456789098765432101234567891_1000000000000000000002 : add_spec 123456789098765432101234567891 1000000000000000000002 123456790098765432101234567893.
Proof.
  unfold add_spec.
  reflexivity.
Qed.