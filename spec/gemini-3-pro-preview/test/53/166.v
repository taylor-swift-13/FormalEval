Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg_101_neg_251: add_spec (-101) (-251) (-352).
Proof.
  unfold add_spec.
  reflexivity.
Qed.