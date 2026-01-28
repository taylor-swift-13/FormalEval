Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg9999_large: add_spec (-9999)%Z 98765432101234567890123456787%Z 98765432101234567890123446788%Z.
Proof.
  unfold add_spec.
  reflexivity.
Qed.