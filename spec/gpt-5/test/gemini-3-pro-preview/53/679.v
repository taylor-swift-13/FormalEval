Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_98765432101234567890123456789_4 : add_spec 98765432101234567890123456789 4 98765432101234567890123456793.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.