Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg9_neg98765432101234567890123456788: add_spec (-9) (-98765432101234567890123456788) (-98765432101234567890123456797).
Proof.
  unfold add_spec.
  reflexivity.
Qed.