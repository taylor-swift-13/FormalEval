Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg249_neg249: add_spec (-249) (-249) (-498).
Proof.
  unfold add_spec.
  reflexivity.
Qed.