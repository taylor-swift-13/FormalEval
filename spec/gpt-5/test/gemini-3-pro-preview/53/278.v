Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_98765432101234567890123456787_98765432101234567890123456787 : add_spec 98765432101234567890123456787 98765432101234567890123456787 197530864202469135780246913574.
Proof.
  unfold add_spec.
  reflexivity.
Qed.