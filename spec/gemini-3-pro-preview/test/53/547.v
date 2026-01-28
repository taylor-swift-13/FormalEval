Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_large: add_spec 1000000000000000000003 (-999999) 999999999999999000004.
Proof.
  unfold add_spec.
  reflexivity.
Qed.