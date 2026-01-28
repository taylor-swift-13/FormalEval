Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg6_neg5: add_spec (-6) (-5) (-11).
Proof.
  unfold add_spec.
  reflexivity.
Qed.