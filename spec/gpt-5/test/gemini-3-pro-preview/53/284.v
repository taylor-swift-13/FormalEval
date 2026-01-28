Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_9998_98765432101234567890123456787 : add_spec 9998 98765432101234567890123456787 98765432101234567890123466785.
Proof.
  unfold add_spec.
  reflexivity.
Qed.