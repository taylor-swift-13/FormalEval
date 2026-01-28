Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_large : add_spec 1000000000000000000002 98765432101234567890123456791 98765433101234567890123456793.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.