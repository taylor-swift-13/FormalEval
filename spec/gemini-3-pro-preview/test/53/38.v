Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_183_272: add_spec 183 272 455.
Proof.
  unfold add_spec.
  reflexivity.
Qed.