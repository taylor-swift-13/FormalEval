Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_2147483647_1: add_spec 2147483647 1 2147483648.
Proof.
  unfold add_spec.
  reflexivity.
Qed.