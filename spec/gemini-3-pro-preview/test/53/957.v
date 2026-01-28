Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_998_neg10002: add_spec 998 (-10002) (-9004).
Proof.
  unfold add_spec.
  reflexivity.
Qed.