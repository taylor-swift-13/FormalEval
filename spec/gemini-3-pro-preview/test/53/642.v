Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg2_neg1000000: add_spec (-2) (-1000000) (-1000002).
Proof.
  unfold add_spec.
  reflexivity.
Qed.