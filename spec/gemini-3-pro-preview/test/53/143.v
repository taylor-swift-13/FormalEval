Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_999_neg2: add_spec 999 (-2) 997.
Proof.
  unfold add_spec.
  reflexivity.
Qed.