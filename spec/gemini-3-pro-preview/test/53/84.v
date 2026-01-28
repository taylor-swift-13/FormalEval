Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_746_105: add_spec 746 105 851.
Proof.
  unfold add_spec.
  reflexivity.
Qed.