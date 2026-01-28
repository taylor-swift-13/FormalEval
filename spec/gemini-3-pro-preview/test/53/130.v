Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg6_neg8: add_spec (-6) (-8) (-14).
Proof.
  unfold add_spec.
  reflexivity.
Qed.