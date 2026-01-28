Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_0_neg99: add_spec 0 (-99) (-99).
Proof.
  unfold add_spec.
  reflexivity.
Qed.