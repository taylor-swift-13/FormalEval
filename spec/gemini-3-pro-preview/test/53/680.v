Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_4_5: add_spec 4 5 9.
Proof.
  unfold add_spec.
  reflexivity.
Qed.