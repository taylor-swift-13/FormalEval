Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg1001_neg1000: add_spec (-1001) (-1000) (-2001).
Proof.
  unfold add_spec.
  reflexivity.
Qed.