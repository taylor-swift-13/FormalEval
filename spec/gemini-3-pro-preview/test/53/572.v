Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg10_large: add_spec (-10) 1000000000000000000002 999999999999999999992.
Proof.
  unfold add_spec.
  reflexivity.
Qed.