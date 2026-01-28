Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg1000_neg251: add_spec (-1000) (-251) (-1251).
Proof.
  unfold add_spec.
  reflexivity.
Qed.