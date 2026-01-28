Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg2147483648_neg1: add_spec (-2147483648) (-1) (-2147483649).
Proof.
  unfold add_spec.
  reflexivity.
Qed.