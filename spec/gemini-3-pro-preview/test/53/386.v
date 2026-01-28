Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_4_4: add_spec 4 4 8.
Proof.
  unfold add_spec.
  reflexivity.
Qed.