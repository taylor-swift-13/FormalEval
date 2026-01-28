Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_5_98765432101234567890123456787 : add_spec 5 98765432101234567890123456787 98765432101234567890123456792.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.