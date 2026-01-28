Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_18_434: add_spec 18 434 452.
Proof.
  unfold add_spec.
  reflexivity.
Qed.