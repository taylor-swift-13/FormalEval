Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg5_neg6: add_spec (-5) (-6) (-11).
Proof.
  unfold add_spec.
  reflexivity.
Qed.