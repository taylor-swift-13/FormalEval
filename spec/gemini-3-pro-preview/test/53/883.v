Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_large_neg: add_spec (-1000000000000000000000) (-101) (-1000000000000000000101).
Proof.
  unfold add_spec.
  reflexivity.
Qed.