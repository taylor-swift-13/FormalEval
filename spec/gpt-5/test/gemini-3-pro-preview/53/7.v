Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_139_579 : add_spec 139 579 718.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.