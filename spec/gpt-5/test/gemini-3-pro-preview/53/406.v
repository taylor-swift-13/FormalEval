Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_98765432101234567890123456786_98765432101234567890123456786 : add_spec 98765432101234567890123456786 98765432101234567890123456786 197530864202469135780246913572.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.