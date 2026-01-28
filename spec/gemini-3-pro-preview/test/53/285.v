Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_9998_neg10000: add_spec 9998 (-10000) (-2).
Proof.
  unfold add_spec.
  reflexivity.
Qed.