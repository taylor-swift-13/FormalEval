Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg10000_neg9999: add_spec (-10000) (-9999) (-19999).
Proof.
  unfold add_spec.
  reflexivity.
Qed.