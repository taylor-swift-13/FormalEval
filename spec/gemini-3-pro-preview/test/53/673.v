Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg8_neg9999: add_spec (-8) (-9999) (-10007).
Proof.
  unfold add_spec.
  reflexivity.
Qed.