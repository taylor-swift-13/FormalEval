Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_99_neg : add_spec 99 (-98765432101234567890123456788) (-98765432101234567890123456689).
Proof.
  unfold add_spec.
  reflexivity.
Qed.