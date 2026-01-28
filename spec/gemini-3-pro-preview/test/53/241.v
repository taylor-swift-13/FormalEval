Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_9999_123456789098765432101234567891: add_spec 9999 123456789098765432101234567891 123456789098765432101234577890.
Proof.
  unfold add_spec.
  reflexivity.
Qed.