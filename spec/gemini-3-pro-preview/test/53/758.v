Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_large: add_spec 98765432101234567890123456790 9998 98765432101234567890123466788.
Proof.
  unfold add_spec.
  reflexivity.
Qed.