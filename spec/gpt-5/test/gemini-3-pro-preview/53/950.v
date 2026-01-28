Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_98765432101234567890123456789_neg98 : add_spec 98765432101234567890123456789 (-98) 98765432101234567890123456691.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.