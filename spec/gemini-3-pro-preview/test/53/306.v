Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg: add_spec (-9999) (-10001) (-20000).
Proof.
  unfold add_spec.
  reflexivity.
Qed.