Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg3_0: add_spec (-3) 0 (-3).
Proof.
  unfold add_spec.
  reflexivity.
Qed.