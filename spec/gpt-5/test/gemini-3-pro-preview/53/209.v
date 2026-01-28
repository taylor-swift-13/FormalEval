Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_large : add_spec (-98765432101234567890123456789) (-123456789098765432101234567890) (-222222221199999999991358024679).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.