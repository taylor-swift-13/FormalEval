Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_1000001_neg11: add_spec 1000001 (-11) 999990.
Proof.
  unfold add_spec.
  reflexivity.
Qed.