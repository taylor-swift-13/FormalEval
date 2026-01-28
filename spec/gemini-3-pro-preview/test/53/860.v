Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg: add_spec (-99) (-1000000000000000000000) (-1000000000000000000099).
Proof.
  unfold add_spec.
  reflexivity.
Qed.