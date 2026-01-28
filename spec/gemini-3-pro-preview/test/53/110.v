Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_999_1: add_spec 999 1 1000.
Proof.
  unfold add_spec.
  reflexivity.
Qed.