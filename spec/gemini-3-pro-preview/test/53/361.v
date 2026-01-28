Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg999996_1000000000000000000: add_spec (-999996) 1000000000000000000 999999999999000004.
Proof.
  unfold add_spec.
  reflexivity.
Qed.