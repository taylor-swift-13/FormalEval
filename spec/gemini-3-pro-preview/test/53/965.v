Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_97_neg999999: add_spec 97 (-999999) (-999902).
Proof.
  unfold add_spec.
  reflexivity.
Qed.