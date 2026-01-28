Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_large_neg: add_spec (-999999999999999999999) (-99) (-1000000000000000000098).
Proof.
  unfold add_spec.
  reflexivity.
Qed.