Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_5_1000: add_spec 5 1000 1005.
Proof.
  unfold add_spec.
  reflexivity.
Qed.