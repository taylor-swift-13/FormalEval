Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_659_191: add_spec 659 191 850.
Proof.
  unfold add_spec.
  reflexivity.
Qed.