Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_1000_big: add_spec 1000 98765432101234567890123456788 98765432101234567890123457788.
Proof.
  unfold add_spec.
  reflexivity.
Qed.