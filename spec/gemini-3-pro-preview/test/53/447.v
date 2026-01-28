Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_4_98765432101234567890123456787: add_spec 4 98765432101234567890123456787 98765432101234567890123456791.
Proof.
  unfold add_spec.
  reflexivity.
Qed.