Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_8_neg249: add_spec 8 (-249) (-241).
Proof.
  unfold add_spec.
  reflexivity.
Qed.