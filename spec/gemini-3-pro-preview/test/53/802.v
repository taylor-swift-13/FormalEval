Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_67_neg99: add_spec 67 (-99) (-32).
Proof.
  unfold add_spec.
  reflexivity.
Qed.