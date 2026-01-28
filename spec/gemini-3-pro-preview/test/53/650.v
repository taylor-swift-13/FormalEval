Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_9999_neg1000000000000000000000: add_spec 9999 (-1000000000000000000000) (-999999999999999990001).
Proof.
  unfold add_spec.
  reflexivity.
Qed.