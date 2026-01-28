Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_704_645: add_spec 704 645 1349.
Proof.
  unfold add_spec.
  reflexivity.
Qed.