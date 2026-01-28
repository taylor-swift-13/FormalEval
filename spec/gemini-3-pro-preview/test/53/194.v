Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg249_neg10: add_spec (-249) (-10) (-259).
Proof.
  unfold add_spec.
  reflexivity.
Qed.