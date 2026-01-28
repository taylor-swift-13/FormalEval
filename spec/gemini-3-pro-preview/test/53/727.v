Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg_999999_neg_10000: add_spec (-999999) (-10000) (-1009999).
Proof.
  unfold add_spec.
  reflexivity.
Qed.