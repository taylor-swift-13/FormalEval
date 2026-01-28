Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_66_neg: add_spec 66 (-1000000000000000000000) (-999999999999999999934).
Proof.
  unfold add_spec.
  reflexivity.
Qed.