Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_191_93: add_spec 191 93 284.
Proof.
  unfold add_spec.
  reflexivity.
Qed.