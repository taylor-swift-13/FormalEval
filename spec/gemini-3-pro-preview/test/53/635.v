Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg99_neg1: add_spec (-99) (-1) (-100).
Proof.
  unfold add_spec.
  reflexivity.
Qed.