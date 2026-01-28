Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_1000000_neg999999: add_spec 1000000 (-999999) 1.
Proof.
  unfold add_spec.
  reflexivity.
Qed.