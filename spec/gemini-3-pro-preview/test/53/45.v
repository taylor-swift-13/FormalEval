Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_860_376: add_spec 860 376 1236.
Proof.
  unfold add_spec.
  reflexivity.
Qed.