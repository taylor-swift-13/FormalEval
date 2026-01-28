Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg12_neg12: add_spec (-12) (-12) (-24).
Proof.
  unfold add_spec.
  reflexivity.
Qed.