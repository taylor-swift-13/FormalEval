Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_1_7: add_spec 1 7 8.
Proof.
  unfold add_spec.
  reflexivity.
Qed.