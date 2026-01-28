Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_10000_neg1000: add_spec 10000 (-1000) 9000.
Proof.
  unfold add_spec.
  reflexivity.
Qed.