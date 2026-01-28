Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_9998_large: add_spec 9998 123456789098765432101234567893 123456789098765432101234577891.
Proof.
  unfold add_spec.
  reflexivity.
Qed.