Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg10001_neg999999: add_spec (-10001) (-999999) (-1010000).
Proof.
  unfold add_spec.
  reflexivity.
Qed.