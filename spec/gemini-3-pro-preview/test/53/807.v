Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg99_9999: add_spec (-99) 9999 9900.
Proof.
  unfold add_spec.
  reflexivity.
Qed.